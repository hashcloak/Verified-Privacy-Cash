import Connection.Proofs.WellFormed
import Connection.Proofs.Bridge
open Aeneas Aeneas.Std Result PrivacyCash.Model

/-! # Proofs: every execution of the code model is a run of the spec

NOT FOR REVIEW: the statements are in `Connection/ConnectionTheorems.lean`. The bridge walks over an
execution from genesis one event at a time, keeping a spec run that matches it so far. Before
`initialize` no program step can succeed. `initialize` starts the spec run at `initWorld`.
Each `transact` extends it by one transaction (the main per-step theorem). Admin instructions
and outside actions are changes allowed between transactions (`LeanSpec.Between.Allowed`).
-/

namespace Connection

/-! ## Whether the pool has been initialized -/

theorem genesis_noProgramAccounts {d : Deployment} {s : State} (h : Genesis d.programId s) :
    NoProgramAccounts d s :=
  ⟨fun k _ hk => h k hk.1, fun k _ hk => h k hk.1, fun k _ hk => h k hk.1⟩

/-! ## Outside actions -/

/-- Outside actions never make an account the program's tree, pool or config. -/
theorem env_noProgramAccounts {d : Deployment} {s s' : State} (h : EnvStep d.programId s s')
    (hn : NoProgramAccounts d s) : NoProgramAccounts d s' := by
  have back : ∀ k x, (s' k).owner = d.programId → (s' k).data = x → x.isProgramData = true →
      (s k).owner = d.programId ∧ (s k).data = x := by
    intro k x ho hd hx
    by_cases hk : (s k).owner = d.programId
    · exact ⟨hk, ((h k).1 hk).2.1 ▸ hd⟩
    · have := (h k).2 hk; rw [hd] at this; simp [hx] at this
  refine ⟨fun k t ht => ?_, fun k p hp => ?_, fun k c hc => ?_⟩
  · exact hn.1 k t (back k _ ht.1 ht.2 rfl)
  · exact hn.2.1 k p (back k _ hp.1 hp.2 rfl)
  · exact hn.2.2 k c (back k _ hc.1 hc.2 rfl)

/-- Outside actions keep the program's tree, pool and config. -/
theorem env_initialized {d : Deployment} {s s' : State} (h : EnvStep d.programId s s')
    (hi : Initialized d s) : Initialized d s' := by
  obtain ⟨⟨t, ht⟩, ⟨p, hp⟩, ⟨c, hc⟩⟩ := hi
  refine ⟨⟨t, ?_⟩, ⟨p, ?_⟩, ⟨c, ?_⟩⟩
  · obtain ⟨o, dd, -⟩ := (h _).1 ht.1; exact ⟨o, dd.trans ht.2⟩
  · obtain ⟨o, dd, -⟩ := (h _).1 hp.1; exact ⟨o, dd.trans hp.2⟩
  · obtain ⟨o, dd, -⟩ := (h _).1 hc.1; exact ⟨o, dd.trans hc.2⟩

/-- Two states with the same spec tree map to worlds that differ only in their balances and
    config. -/
theorem toWorld_between_of_same_tree {d : Deployment} {rent : Nat → U64} {spent : Finset LeanSpec.F}
    {s s' : State} (ht : toTree (treeAt s' (treeAddr d)) = toTree (treeAt s (treeAddr d))) :
    toWorld d rent spent s' = (toWorld d rent spent s).between
      (LeanSpec.Between.unchanged (toWorld d rent spent s')) := by
  simp only [toWorld, LeanSpec.World.between, LeanSpec.Between.unchanged, ht]

/-- **Outside actions are changes allowed between transactions.** The program's data is
    untouched, and the pool only gains lamports. -/
theorem env_between {d : Deployment} {rent : Nat → U64} {spent : Finset LeanSpec.F} {s s' : State}
    (h : EnvStep d.programId s s') (hi : Initialized d s) :
    toWorld d rent spent s' = (toWorld d rent spent s).between
        (LeanSpec.Between.unchanged (toWorld d rent spent s')) ∧
      (LeanSpec.Between.unchanged (toWorld d rent spent s')).Allowed (toWorld d rent spent s) := by
  obtain ⟨⟨t, ht⟩, ⟨p, hp⟩, ⟨c, hc⟩⟩ := hi
  have dt := ((h _).1 ht.1).2.1
  have dc := ((h _).1 hc.1).2.1
  have hw := toWorld_between_of_same_tree (d := d) (rent := rent) (spent := spent) (s := s) (s' := s')
    (by simp only [treeAt, dt])
  refine ⟨hw, ⟨?_, ?_⟩⟩
  · obtain ⟨-, dp, lp⟩ := (h _).1 hp.1
    show publicBalance s (fromPubkey (toPubkey (poolAddr d)))
      ≤ publicBalance s' (fromPubkey (toPubkey (poolAddr d)))
    rw [fromPubkey_toPubkey]
    simp only [publicBalance, dp, hp.2]
    exact lp
  · have : (toWorld d rent spent s').state.config = (toWorld d rent spent s).state.config := by
      simp only [toWorld, treeAt, configAt, dt, dc]
    show LeanSpec.AdminChanges _ (toWorld d rent spent s').state.config
    rw [this]; exact .none _

/-! ## Admin instructions -/

/-- What `update_global_config` computes: each given setting replaces the old one, and the
    error margin, when given, is at most 10000. -/
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
    the config's authority, with an error margin of at most 10000; nothing else changes. -/
theorem ugc_between {d : Deployment} {rent : Nat → U64} {spent : Finset LeanSpec.F} {s s' : State}
    {tx : TxEnv} {a : UpdateGlobalConfigAccounts} {dep wd m : Option U16}
    (wf : WellFormed d spent s) (hi : Initialized d s)
    (h : execUpdateGlobalConfig d s tx a dep wd m = .ok s') :
    Initialized d s' ∧
      toWorld d rent spent s' = (toWorld d rent spent s).between
        (LeanSpec.Between.unchanged (toWorld d rent spent s')) ∧
      (LeanSpec.Between.unchanged (toWorld d rent spent s')).Allowed (toWorld d rent spent s) := by
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
  obtain ⟨hc', hmv⟩ := ugc_spec config config' dep wd m (ofResult_ok hres)
  obtain ⟨⟨t, ht⟩, ⟨p, hp⟩, -⟩ := hi
  have hne : treeAddr d ≠ a.globalConfig := fun e => by
    have h1 := ht.2; rw [e, hval.globalConfig.1.2] at h1; cases h1
  have hpne : poolAddr d ≠ a.globalConfig := fun e => by
    have h1 := hp.2; rw [e, hval.globalConfig.1.2] at h1; cases h1
  set s' := s.set a.globalConfig { s a.globalConfig with data := .globalConfig config' } with hs'
  have keep : ∀ k, k ≠ a.globalConfig → s' k = s k := fun k hk => set_data_other hk
  have hkey : s' a.globalConfig = { s a.globalConfig with data := .globalConfig config' } := by simp [hs']
  have htree : treeAt s' (treeAddr d) = treeAt s (treeAddr d) := by
    simp only [treeAt, keep _ hne]
  refine ⟨⟨⟨t, by unfold HoldsTree; rw [keep _ hne]; exact ht⟩, ⟨p, by unfold HoldsTreeToken; rw [keep _ hpne]; exact hp⟩,
    ⟨config', ?_⟩⟩, toWorld_between_of_same_tree (by rw [htree]), ⟨?_, ?_⟩⟩
  · unfold HoldsGlobalConfig; rw [← hka, hkey]; exact ⟨hval.globalConfig.1.1, rfl⟩
  · -- balances: unchanged
    show publicBalance s (fromPubkey (toPubkey (poolAddr d)))
      ≤ publicBalance s' (fromPubkey (toPubkey (poolAddr d)))
    simp only [fromPubkey_toPubkey, publicBalance, keep _ hpne, le_refl]
  · -- config: one allowed admin change
    have hcfg : configAt s (configAddr d) = config := by
      simp only [configAt, ← hka, hval.globalConfig.1.2]
    have hcfg' : configAt s' (configAddr d) = config' := by
      simp only [configAt, ← hka, hkey]
    show LeanSpec.AdminChanges (toConfig (configAt s (configAddr d)) (treeAt s (treeAddr d)))
      (toConfig (configAt s' (configAddr d)) (treeAt s' (treeAddr d)))
    rw [hcfg, hcfg', htree]
    refine .change ⟨tx.signers.map toPubkey,
      .feeSettings (dep.getD config.deposit_fee_rate).val (wd.getD config.withdrawal_fee_rate).val
        (m.getD config.fee_error_margin).val⟩ ?_ (.none _)
    have hsig : toPubkey config.authority ∈ tx.signers.map toPubkey := by
      rw [hval.globalConfig.2.2]; exact List.mem_map_of_mem hval.authority
    have hmarg : (m.getD config.fee_error_margin).val ≤ 10000 := by
      rcases m with _ | v
      · exact hm0
      · exact hmv v rfl
    simp only [LeanSpec.AdminChange.apply, toConfig, if_pos (And.intro hsig hmarg), hc']

/-- **`update_deposit_limit` is an allowed admin change.** It sets the deposit limit, signed by
    the tree's authority; the spec's tree and everything else are unchanged. -/
theorem udl_between {d : Deployment} {rent : Nat → U64} {spent : Finset LeanSpec.F} {s s' : State}
    {tx : TxEnv} {a : UpdateDepositLimitAccounts} {newLimit : U64}
    (wf : WellFormed d spent s) (hi : Initialized d s)
    (h : execUpdateDepositLimit d s tx a newLimit = .ok s') :
    Initialized d s' ∧
      toWorld d rent spent s' = (toWorld d rent spent s).between
        (LeanSpec.Between.unchanged (toWorld d rent spent s')) ∧
      (LeanSpec.Between.unchanged (toWorld d rent spent s')).Allowed (toWorld d rent spent s) := by
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
  have hpne : poolAddr d ≠ a.treeAccount := fun e => by
    have h1 := hp.2; rw [e, hval.treeAccount.1.2] at h1; cases h1
  have hcne : configAddr d ≠ a.treeAccount := fun e => by
    have h1 := hc.2; rw [e, hval.treeAccount.1.2] at h1; cases h1
  set s' := s.set a.treeAccount { s a.treeAccount with data := .treeAccount tree' } with hs'
  have keep : ∀ k, k ≠ a.treeAccount → s' k = s k := fun k hk => set_data_other hk
  have hkey : s' a.treeAccount = { s a.treeAccount with data := .treeAccount tree' } := by simp [hs']
  have hT : treeAt s (treeAddr d) = tree := by simp only [treeAt, ← hka, hval.treeAccount.1.2]
  have hT' : treeAt s' (treeAddr d) = tree' := by simp only [treeAt, ← hka, hkey]
  have hC : configAt s' (configAddr d) = configAt s (configAddr d) := by
    simp only [configAt, keep _ hcne]
  refine ⟨⟨⟨tree', ?_⟩, ⟨p, by unfold HoldsTreeToken; rw [keep _ hpne]; exact hp⟩, ⟨c, by unfold HoldsGlobalConfig; rw [keep _ hcne]; exact hc⟩⟩,
    toWorld_between_of_same_tree (by rw [hT, hT', ht']; rfl), ⟨?_, ?_⟩⟩
  · unfold HoldsTree; rw [← hka, hkey]; exact ⟨hval.treeAccount.1.1, rfl⟩
  · show publicBalance s (fromPubkey (toPubkey (poolAddr d)))
      ≤ publicBalance s' (fromPubkey (toPubkey (poolAddr d)))
    simp only [fromPubkey_toPubkey, publicBalance, keep _ hpne, le_refl]
  · show LeanSpec.AdminChanges (toConfig (configAt s (configAddr d)) (treeAt s (treeAddr d)))
      (toConfig (configAt s' (configAddr d)) (treeAt s' (treeAddr d)))
    rw [hC, hT, hT', ht']
    refine .change ⟨tx.signers.map toPubkey, .depositLimit newLimit.val⟩ ?_ (.none _)
    have hsig : toPubkey tree.authority ∈ tx.signers.map toPubkey := by
      rw [hval.treeAccount.2.2]; exact List.mem_map_of_mem hval.authority
    simp only [LeanSpec.AdminChange.apply, toConfig, if_pos hsig]

/-! ## `transact` -/

/-- `transact` keeps the program's tree, pool and config (it rewrites the tree's data and creates
    two nullifier accounts elsewhere). -/
theorem transact_initialized {d : Deployment} {spent : Finset LeanSpec.F} {s s' : State} {tx : TxEnv}
    {a : TransactAccounts} {proof : zkcash_core.transact.Proof} {ext : I64} {fee : U64}
    {out1 out2 : Slice U8} {evs : List CommitmentData}
    (wf : WellFormed d spent s) (hi : Initialized d s)
    (h : step d s tx (.transact a proof ext fee out1 out2) = .ok (s', evs)) : Initialized d s' := by
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
  have htA : a.treeAccount = treeAddr d := (wf.tree _ _ hvalid.treeAccount.1).1
  have s'_other : ∀ k, k ≠ a.treeAccount → (s' k).owner = (s₁ k).owner ∧ (s' k).data = (s₁ k).data := by
    intro k hk; rw [hs']; simp [State.set, hk, State.withBalances]
  have hpt : poolAddr d ≠ a.treeAccount := fun e => by
    have h1 := hp.2; rw [e, hvalid.treeAccount.1.2] at h1; cases h1
  have hct : configAddr d ≠ a.treeAccount := fun e => by
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
    obtain ⟨zb', hzi', hzbv⟩ := okOfE (Std.Array.index_usize_spec z it.start (by simp <;> omega))
    rw [hzi'] at hzi; obtain rfl := Result.ok_injective hzi
    obtain ⟨a2, ha2, hr⟩ := bindOk hr
    obtain ⟨a2', ha2', ha2v⟩ := okOfE (Std.Array.update_spec a it.start zb' (by simp <;> omega))
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
      · rw [getElem!_pos _ _ (by simp <;> omega)]; simp only [hji, List.getElem_set_self]
        rw [hzbv, getElem!_pos _ _ (by simp <;> omega)]
      · rw [getElem!_pos _ _ (by simp <;> omega)]
        have := ha j (by omega)
        rw [getElem!_pos _ _ (by simp <;> omega)] at this
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
  obtain ⟨ir', hir', hirv⟩ := okOfE (Std.Array.index_usize_spec z hgt (by simp <;> omega))
  rw [hir'] at hir; obtain rfl := Result.ok_injective hir
  obtain ⟨a1', ha1', ha1v⟩ := okOfE (Std.Array.update_spec t0.root_history 0#usize ir' (by simp))
  rw [ha1'] at ha1; obtain rfl := Result.ok_injective ha1
  have hir26 : ir' = z.val[26]! := by
    simp [hirv, hgv, List.getElem!_eq_getElem?_getD]
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
  simp only [toF, hb, Nat.cast_zero]

/-- **The tree `initialize` writes is the spec's empty tree** (`LeanSpec.initTree`), when the
    code's zero hashes are the spec's (`HashesAgree.zeroBytes`). -/
theorem initialize_toTree [LeanSpec.PoseidonHashes] {H : zkcash_core.merkle_tree.Hasher Unit}
    {t : zkcash_core.merkle_tree.MerkleTreeAccount} {auth : Pubkey} {b : U8} {m : U64}
    {r : core.result.Result Unit zkcash_core.error.ErrorCode}
    (hz : ∃ z, H.zero_bytes = ok z ∧ ∀ i, i ≤ 26 → toF (z.val[i]!) = LeanSpec.Z i)
    (h : zkcash_core.admin.init_tree H zeroTree auth b m = ok (r, t)) :
    toTree t = LeanSpec.initTree := by
  obtain ⟨z, hzb, hzv⟩ := hz
  obtain ⟨hsub, hroot, hhist, hni, hri, -, -⟩ := initTree_values hzb h
  have hzero : ∀ j : ℕ, j < 100 → zeroTree.root_history.val[j]! = Std.Array.repeat 32#usize 0#u8 := by
    intro j hj
    rw [getElem!_pos _ _ (by simp <;> omega)]
    simp only [zeroTree, Std.Array.repeat_val, List.getElem_replicate]
  simp only [toTree, LeanSpec.initTree, LeanSpec.Tree.mk.injEq]
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

/-- What `admin::initialize` returns when it succeeds: the tree `init_tree` wrote, a pool and a
    config whose authority is the caller, with fee rates 0 and 25 and error margin 500. -/
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
      core.convert.FromSame, Result.ok.injEq] at hr1
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
    when the deployment has one, the error margin is 500, the tree is the spec's empty tree. SOL
    already at the pool's address counts as sent to it before the first transaction (allowed). -/
theorem init_between [LeanSpec.PoseidonHashes] {d : Deployment} {rent : Nat → U64} {s s' : State}
    {tx : TxEnv} {a : InitializeAccounts}
    (hdist : treeAddr d ≠ poolAddr d ∧ treeAddr d ≠ configAddr d ∧ poolAddr d ≠ configAddr d)
    (hpid : d.programId ≠ systemProgram) (hrent : tx.minimumBalance = some rent)
    (hz : ∃ z, d.crypto.hasher.zero_bytes = ok z ∧ ∀ i, i ≤ 26 → toF (z.val[i]!) = LeanSpec.Z i)
    (h : execInitialize d s tx a = .ok s') :
    Initialized d s' ∧ ∃ params : LeanSpec.InitParams,
      params.pool = toPubkey (poolAddr d) ∧ params.rentExemptMin = (rent treeTokenAccountSpace).val ∧
      params.nullifierRent = (rent nullifierAccountSpace).val ∧
      params.admin = d.adminPubkey.map toPubkey ∧
      toWorld d rent ∅ s' = (LeanSpec.initWorld params).between
        (LeanSpec.Between.unchanged (toWorld d rent ∅ s')) ∧
      (LeanSpec.Between.unchanged (toWorld d rent ∅ s')).Allowed (LeanSpec.initWorld params) := by
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
  have htA : a.treeAccount = treeAddr d := hvalid.treeAccount.1
  have hpA : a.treeTokenAccount = poolAddr d := hvalid.treeTokenAccount.1
  have hcA : a.globalConfig = configAddr d := hvalid.globalConfig.1
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
  have dT : (s' (treeAddr d)).data = .treeAccount tree := by
    rw [← htA, (hs'k _).2.2, if_neg dtc, if_neg dtp, if_pos rfl]
  have dP : (s' (poolAddr d)).data = .treeToken token := by
    rw [← hpA, (hs'k _).2.2, if_neg dpc, if_pos rfl]
  have dC : (s' (configAddr d)).data = .globalConfig config := by
    rw [← hcA, (hs'k _).2.2, if_pos rfl]
  have hT : treeAt s' (treeAddr d) = tree := by simp only [treeAt, dT]
  have hC : configAt s' (configAddr d) = config := by simp only [configAt, dC]
  have hinit : Initialized d s' := by
    refine ⟨⟨tree, ?_, dT⟩, ⟨token, ?_, dP⟩, ⟨config, ?_, dC⟩⟩
    · rw [← htA, (hs'k _).1]; exact own1
    · rw [← hpA, (hs'k _).1]; exact own2
    · rw [← hcA, (hs'k _).1]; exact own3
  have hcfg : (toWorld d rent ∅ s').state.config = toConfig config tree := by
    simp only [toWorld, hT, hC]
  have pa : (toConfig config tree).authority = toPubkey a.authority := by simp [toConfig, hc]
  have pl : (toConfig config tree).limitAuthority = toPubkey a.authority := by simp [toConfig, hauth]
  have pad : ∀ x, d.adminPubkey.map toPubkey = some x → toPubkey a.authority = x := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp hx
    rw [hadmin k hk]
  have pm : (toConfig config tree).feeMarginError ≤ 10000 := by simp [toConfig, hc]
  refine ⟨hinit, ⟨toConfig config tree, (toWorld d rent ∅ s').balances, (rent treeTokenAccountSpace).val,
    (rent nullifierAccountSpace).val, toPubkey (poolAddr d), toPubkey a.authority,
    d.adminPubkey.map toPubkey, pa, pl, pad, pm⟩, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp only [toWorld, LeanSpec.initWorld, LeanSpec.World.between, LeanSpec.Between.unchanged, hT,
      htree]
  · -- the pool gained at least nothing
    show (LeanSpec.initWorld _).poolBalance ≤ publicBalance s' (fromPubkey (toPubkey (poolAddr d)))
    simp only [LeanSpec.World.poolBalance, LeanSpec.initWorld, Function.update_self,
      fromPubkey_toPubkey, publicBalance, dP]
    rw [← hpA, (hs'k _).2.1]; exact hpl
  · show LeanSpec.AdminChanges (toConfig config tree) (toWorld d rent ∅ s').state.config
    rw [hcfg]; exact .none _

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
    exact hn.2.2 _ _ (not_not.mp hv).globalConfig.1
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
  rw [← ht.1, show treeAddr d = a.treeAccount from hvalid.treeAccount.1.symm]
  exact hvalid.treeAccount.2.1

/-! ## The bridge, one event at a time -/

section
variable [LeanSpec.PoseidonHashes] [LeanSpec.Sha] {G1 G2 GT : Type} [AddCommGroup G1]
  [Module LeanSpec.F G1] [AddCommGroup G2] [Module LeanSpec.F G2] [CommGroup GT]

/-- What the bridge keeps along an execution. -/
def BridgeInv (d : Deployment) (rent : Nat → U64) (C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT)
    (laws : PairingLaws C.e) (spent : Finset LeanSpec.F) (txs : List LeanSpec.TxInputs) (s : State) :
    Prop :=
  WellFormed d spent s ∧
    ((NoProgramAccounts d s ∧ txs = [] ∧ spent = ∅) ∨
      (Initialized d s ∧
        letI : LeanSpec.Groups := syscallGroups C
        letI : LeanSpec.Pairing := syscallPairing C laws
        letI : LeanSpec.Deployment := ⟨programKey C⟩
        IsSpecRun d rent spent txs s))

/-- A change between transactions after the end of a spec run. -/
theorem IsSpecRun.between {d : Deployment} {rent : Nat → U64}
    {C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT} {laws : PairingLaws C.e}
    {spent : Finset LeanSpec.F} {txs : List LeanSpec.TxInputs} {s s' : State}
    (h : letI : LeanSpec.Groups := syscallGroups C
      letI : LeanSpec.Pairing := syscallPairing C laws
      letI : LeanSpec.Deployment := ⟨programKey C⟩
      IsSpecRun d rent spent txs s)
    (hw : toWorld d rent spent s' = (toWorld d rent spent s).between
      (LeanSpec.Between.unchanged (toWorld d rent spent s')))
    (ha : (LeanSpec.Between.unchanged (toWorld d rent spent s')).Allowed (toWorld d rent spent s)) :
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C laws
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    IsSpecRun d rent spent txs s' := by
  letI : LeanSpec.Groups := syscallGroups C
  letI : LeanSpec.Pairing := syscallPairing C laws
  letI : LeanSpec.Deployment := ⟨programKey C⟩
  obtain ⟨params, r, h1, h2, h3, h4, htx, b, hb, heq⟩ := h
  refine ⟨params, r, h1, h2, h3, h4, htx, LeanSpec.Between.unchanged (toWorld d rent spent s'), ?_, ?_⟩
  · rw [heq] at ha
    exact hb.trans ha
  · rw [hw, heq]; rfl

/-- **Outside actions keep the invariant.** -/
theorem bridge_env {d : Deployment} {rent : Nat → U64}
    {C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT} {laws : PairingLaws C.e}
    {spent : Finset LeanSpec.F} {txs : List LeanSpec.TxInputs} {s s' : State}
    (hinv : BridgeInv d rent C laws spent txs s) (h : EnvStep d.programId s s') :
    BridgeInv d rent C laws spent txs s' := by
  obtain ⟨wf, hn | ⟨hi, hr⟩⟩ := hinv
  · exact ⟨wf_envStep wf h, Or.inl ⟨env_noProgramAccounts h hn.1, hn.2⟩⟩
  · obtain ⟨hw, ha⟩ := env_between (rent := rent) (spent := spent) h hi
    exact ⟨wf_envStep wf h, Or.inr ⟨env_initialized h hi, hr.between hw ha⟩⟩

/-- The program's three fixed accounts differ (from `ExecutionAssumptions.fixedAddressesDiffer`). -/
theorem fixed_addresses_differ {d : Deployment} {rent : Nat → U64} {s₀ : State} {evs : List Event}
    (assume : ExecutionAssumptions d rent s₀ evs) :
    treeAddr d ≠ poolAddr d ∧ treeAddr d ≠ configAddr d ∧ poolAddr d ≠ configAddr d :=
  singleton_pdas_distinct _ _ _ assume.fixedAddressesDiffer

/-- **Each instruction keeps the invariant.** `initialize` starts the spec run; `transact`
    extends it by its transaction (the main per-step theorem); the admin instructions are
    allowed changes between transactions. -/
theorem bridge_step {d : Deployment} {rent : Nat → U64}
    {C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT} {laws : PairingLaws C.e}
    {spent : Finset LeanSpec.F} {txs : List LeanSpec.TxInputs} {s s' : State} {tx : TxEnv}
    {ix : Instruction} {em : List CommitmentData}
    (hinv : BridgeInv d rent C laws spent txs s)
    (hpid : d.programId ≠ systemProgram) (hashes : HashesAgree d.crypto)
    (hdist : treeAddr d ≠ poolAddr d ∧ treeAddr d ≠ configAddr d ∧ poolAddr d ≠ configAddr d)
    (hstepA : StepAssumptions d rent tx ix) (h : step d s tx ix = .ok (s', em)) :
    BridgeInv d rent C laws (spent ∪ stepSpent ix) (txs ++ stepTxs ix) s' := by
  letI : LeanSpec.Groups := syscallGroups C
  letI : LeanSpec.Pairing := syscallPairing C laws
  letI : LeanSpec.Deployment := ⟨programKey C⟩
  obtain ⟨wf, hn | ⟨hi, hr⟩⟩ := hinv
  · -- before initialization: only `initialize` succeeds, and it starts the spec run
    have wf' := wf_step hashes.poseidonCanonical hashes.zeroBytesCanonical wf h
    obtain ⟨a, rfl⟩ := noProgram_step hn.1 h
    obtain ⟨s₁, h1, h2⟩ := PrivacyCash.Model.Except.bind_ok h
    cases h2
    obtain ⟨hi', params, hp1, hp2, hp3, hp4, heq, ha⟩ := init_between hdist
      hpid hstepA hashes.zeroBytes h1
    obtain ⟨-, rfl, rfl⟩ := hn
    refine ⟨wf', Or.inr ⟨hi', ?_⟩⟩
    refine ⟨params, LeanSpec.Run.empty _, hp1, hp2, hp3, hp4, by simp [stepTxs],
      LeanSpec.Between.unchanged (toWorld d rent ∅ s'), ha, ?_⟩
    simpa [stepSpent] using heq
  · cases ix with
    | «initialize» a => exact (initialized_no_initialize hpid hi h).elim
    | updateDepositLimit a l =>
      have wf' := wf_step hashes.poseidonCanonical hashes.zeroBytesCanonical wf h
      obtain ⟨s₁, h1, h2⟩ := PrivacyCash.Model.Except.bind_ok h
      cases h2
      obtain ⟨hi', hw, ha⟩ := udl_between (rent := rent) wf hi h1
      simp only [stepSpent, Finset.union_empty, stepTxs, List.append_nil] at wf' ⊢
      exact ⟨wf', Or.inr ⟨hi', hr.between hw ha⟩⟩
    | updateGlobalConfig a dep wd m =>
      have wf' := wf_step hashes.poseidonCanonical hashes.zeroBytesCanonical wf h
      obtain ⟨s₁, h1, h2⟩ := PrivacyCash.Model.Except.bind_ok h
      cases h2
      obtain ⟨hi', hw, ha⟩ := ugc_between (rent := rent) wf hi h1
      simp only [stepSpent, Finset.union_empty, stepTxs, List.append_nil] at wf' ⊢
      exact ⟨wf', Or.inr ⟨hi', hr.between hw ha⟩⟩
    | transact a proof ext fee out1 out2 =>
      obtain ⟨solana, crypto, hrent⟩ := hstepA
      obtain ⟨b₁, hb₁, b₂, htx, hb₂, wf'⟩ :=
        transact_refines_between_verified C laws h hashes wf solana crypto hrent
      have hi' := transact_initialized wf hi h
      obtain ⟨params, r, hp1, hp2, hp3, hp4, htxs, b, hb, heq⟩ := hr
      rw [heq] at htx hb₁
      rw [LeanSpec.World.between_between] at htx
      obtain ⟨r', hr'tx, hr'f, -⟩ := r.snoc b₁ (hb.trans hb₁) _ _ htx
      refine ⟨wf', Or.inr ⟨hi', params, r', hp1, hp2, hp3, hp4, ?_, LeanSpec.Between.unchanged
        (toWorld d rent (spent ∪ stepSpent (.transact a proof ext fee out1 out2)) s'), ?_, ?_⟩⟩
      · rw [hr'tx, htxs]; rfl
      · rw [hr'f]; exact hb₂
      · rw [hr'f, LeanSpec.World.between_between]; exact (LeanSpec.World.between_self _).symm

/-- **The invariant holds along any execution**, from any state where it holds. -/
theorem bridge_run {d : Deployment} {rent : Nat → U64}
    {C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT} {laws : PairingLaws C.e} {s₀ : State}
    {all : List Event} (hpid : d.programId ≠ systemProgram)
    (hashes : HashesAgree d.crypto) (assume : ExecutionAssumptions d rent s₀ all) :
    ∀ {s s' : State} {evs pre : List Event} {spent : Finset LeanSpec.F} {txs : List LeanSpec.TxInputs},
      all = pre ++ evs → Run d s₀ pre s → BridgeInv d rent C laws spent txs s → Run d s evs s' →
      BridgeInv d rent C laws (spent ∪ runSpent evs) (txs ++ runTxs evs) s' := by
  intro s s' evs pre spent txs hall hpre hinv hrun
  induction hrun generalizing pre spent txs with
  | nil => simpa [runSpent, runTxs] using hinv
  | @program s₁ s₂ s₃ tx ix emitted events hstep _ ih =>
    have hA := assume.eachStep pre events s₁ tx ix emitted hall hpre
    have hinv' := bridge_step hinv hpid hashes (fixed_addresses_differ assume) hA hstep
    have := ih (by rw [hall]; simp) (hpre.append (.program hstep (.nil _))) hinv'
    simpa [runSpent, runTxs, Finset.union_assoc, List.append_assoc] using this
  | @env s₁ s₂ s₃ events henv _ ih =>
    have := ih (by rw [hall]; simp) (hpre.append (.env henv (.nil _))) (bridge_env hinv henv)
    simpa [runSpent, runTxs] using this

/-- **The bridge.** Every execution of the code model from genesis either has not initialized
    the pool, or is (read through `toWorld` and `runTxs`) a run of the spec from the start world
    `initialize` set, up to what happened after its last transaction. -/
theorem execution_is_spec_run_pf {d : Deployment} {rent : Nat → U64} {s₀ s : State} {evs : List Event}
    (hgen : Genesis d.programId s₀) (hrun : Run d s₀ evs s) (hpid : d.programId ≠ systemProgram)
    (C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT) (laws : PairingLaws C.e)
    (hashes : HashesAgree d.crypto) (assume : ExecutionAssumptions d rent s₀ evs) :
    (NoProgramAccounts d s ∧ runTxs evs = []) ∨
      (letI : LeanSpec.Groups := syscallGroups C
       letI : LeanSpec.Pairing := syscallPairing C laws
       letI : LeanSpec.Deployment := ⟨programKey C⟩
       IsSpecRun d rent (runSpent evs) (runTxs evs) s) := by
  have h0 : BridgeInv d rent C laws ∅ [] s₀ :=
    ⟨wf_genesis hgen hpid, Or.inl ⟨genesis_noProgramAccounts hgen, rfl, rfl⟩⟩
  have := bridge_run (C := C) (laws := laws) hpid hashes assume (by simp) (.nil _) h0 hrun
  simp only [Finset.empty_union, List.nil_append] at this
  rcases this.2 with ⟨hn, ht, -⟩ | ⟨-, hr⟩
  · exact Or.inl ⟨hn, ht⟩
  · exact Or.inr hr

/-- Assumptions for an execution hold for any prefix of it. -/
theorem ExecutionAssumptions.prefix {d : Deployment} {rent : Nat → U64} {s₀ : State}
    {evs more : List Event} (h : ExecutionAssumptions d rent s₀ (evs ++ more)) :
    ExecutionAssumptions d rent s₀ evs :=
  ⟨h.fixedAddressesDiffer, fun pre post s tx ix em he hr =>
    h.eachStep pre (post ++ more) s tx ix em (by rw [he]; simp) hr⟩

/-- An initialized execution is a spec run (the bridge, without its "not initialized" case). -/
theorem code_spec_run {d : Deployment} {rent : Nat → U64} {s₀ s : State} {evs : List Event}
    (hgen : Genesis d.programId s₀) (hrun : Run d s₀ evs s) (hpid : d.programId ≠ systemProgram)
    (C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT) (laws : PairingLaws C.e)
    (hashes : HashesAgree d.crypto) (assume : ExecutionAssumptions d rent s₀ evs) (hi : Initialized d s) :
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C laws
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    IsSpecRun d rent (runSpent evs) (runTxs evs) s := by
  rcases execution_is_spec_run_pf hgen hrun hpid C laws hashes assume with ⟨hn, -⟩ | hr
  · obtain ⟨⟨t, ht⟩, -, -⟩ := hi; exact (hn.1 _ _ ht).elim
  · exact hr

/-- **What the spec proves of all its runs holds of an initialized execution's run.** -/
theorem run_satisfies {d : Deployment} {rent : Nat → U64} {s₀ s : State} {evs : List Event}
    (hgen : Genesis d.programId s₀) (hrun : Run d s₀ evs s) (hpid : d.programId ≠ systemProgram)
    (C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT) (laws : PairingLaws C.e)
    (hashes : HashesAgree d.crypto) (assume : ExecutionAssumptions d rent s₀ evs) (hi : Initialized d s) :
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C laws
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    ∀ (P : ∀ params : LeanSpec.InitParams, LeanSpec.Run (LeanSpec.initWorld params) → Prop),
      (∀ params r, P params r) →
      ∃ (params : LeanSpec.InitParams) (r : LeanSpec.Run (LeanSpec.initWorld params)),
        IsRunOf d rent (runSpent evs) (runTxs evs) s params r ∧ P params r := by
  letI : LeanSpec.Groups := syscallGroups C
  letI : LeanSpec.Pairing := syscallPairing C laws
  letI : LeanSpec.Deployment := ⟨programKey C⟩
  intro P hP
  obtain ⟨params, r, h⟩ := code_spec_run hgen hrun hpid C laws hashes assume hi
  exact ⟨params, r, h, hP params r⟩

/-- The per-transaction connection, for a `transact` in an execution from genesis. -/
theorem transact_connection_pf {d : Deployment} {rent : Nat → U64} {s₀ s s' : State}
    {evs : List Event} {tx : TxEnv} {a : TransactAccounts} {proof : zkcash_core.transact.Proof}
    {extAmount : I64} {fee : U64} {out1 out2 : Slice U8} {events : List CommitmentData}
    (hgen : Genesis d.programId s₀) (hrun : Run d s₀ evs s) (hpid : d.programId ≠ systemProgram)
    (hstep : step d s tx (.transact a proof extAmount fee out1 out2) = .ok (s', events))
    (C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT) (laws : PairingLaws C.e)
    (hashes : HashesAgree d.crypto) (solana : SolanaFacts d rent tx out1 out2)
    (crypto : CryptoFacts d proof) (outside : OutsideSpecDetail d rent s tx a proof) :
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C laws
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    let inputs := toInputs a proof extAmount fee out1 out2
    LeanSpec.transact inputs (toWorld d rent (runSpent evs) s)
      (toWorld d rent (runSpent evs ∪ {inputs.k0, inputs.k1}) s') :=
  (transact_refines_verified C laws hstep hashes (wf_reachable hgen hrun hpid hashes) solana crypto
    outside).1

end

end Connection
