import Connection.Proofs.Execution
import Connection.Proofs.StepComplete
open Aeneas Aeneas.Std Result PrivacyCash.Model

/-! # Proofs: completeness over runs

NOT FOR REVIEW. Every spec run (of this deployment, without transactions of findings L1 and A0)
is the image of a code execution: `initialize`, the admin instructions and the outside actions
can do every change the spec allows between transactions, and `transact` every transaction.

The execution is built step by step. It keeps every account either the program's (owned by it,
with one of its account types) or a plain system account (`Tidy`), which gives the premises of
`transact`'s completeness (`PdasOnlyByProgram`, `SignerIsPlain`). -/

namespace Connection

/-! ## Spec transactions as code transactions -/

/-- `fromSpecAccounts d inputs`: the accounts the code transaction lists: the tree, pool and
    config, the four nullifier addresses (as Anchor requires), and the spec's signer, recipient
    and fee recipient. -/
def fromSpecAccounts (d : Deployment) (inputs : Spec.TxInputs) : TransactAccounts where
  treeAccount := d.treeAddress
  nullifier0 := d.pda (nullifier0Seeds (fromSpecProof inputs).input_nullifiers.val[0]!)
  nullifier1 := d.pda (nullifier1Seeds (fromSpecProof inputs).input_nullifiers.val[1]!)
  nullifier2 := d.pda (nullifier0Seeds (fromSpecProof inputs).input_nullifiers.val[1]!)
  nullifier3 := d.pda (nullifier1Seeds (fromSpecProof inputs).input_nullifiers.val[0]!)
  treeTokenAccount := d.poolAddress
  globalConfig := d.configAddress
  recipient := fromPubkey inputs.A
  feeRecipientAccount := fromPubkey inputs.t
  signer := fromPubkey inputs.s
  systemProgram := systemProgram

/-- `fromSpecTransact d inputs`: the code's `transact` for a spec transaction, with the external
    amount as an `i64` and the fee as a `u64`. -/
def fromSpecTransact (d : Deployment) (inputs : Spec.TxInputs) : Instruction :=
  .transact (fromSpecAccounts d inputs) (fromSpecProof inputs) ⟨BitVec.ofInt 64 inputs.extAmt⟩
    ⟨BitVec.ofNat 64 inputs.f⟩ (toSlice inputs.encOut0) (toSlice inputs.encOut1)

/-! ## The code's `initialize` returns -/

theorem checkAdmin_complete {auth : Pubkey} {adm : Option Pubkey}
    (h : ∀ k, adm = some k → auth = k) : zkcash_core.admin.check_admin auth adm = ok (.Ok ()) := by
  unfold zkcash_core.admin.check_admin
  cases adm with
  | none => rfl
  | some k =>
    simp only
    obtain ⟨b, hb, hiff⟩ := (WP.spec_equiv_exists _ _).mp (arrayEqU8Spec auth k)
    rw [hb, bind_tc_ok]
    have : b = true := hiff.mpr (h k rfl)
    subst this; rfl

theorem initTree_complete {H : zkcash_core.merkle_tree.Hasher Unit}
    {z : Std.Array (Std.Array U8 32#usize) 41#usize} (hzb : H.zero_bytes = ok z)
    (t0 : zkcash_core.merkle_tree.MerkleTreeAccount) (auth : Pubkey) (b : U8) (m : U64) :
    ∃ t, zkcash_core.admin.init_tree H t0 auth b m = ok (.Ok (), t) := by
  have hspec : zkcash_core.admin.init_tree H t0 auth b m ⦃ r => r.1 = .Ok () ⦄ := by
    unfold zkcash_core.admin.init_tree zkcash_core.merkle_tree.initialize
    step*
    rw [hzb, bind_tc_ok]
    have hh : height.val = 26 := by
      simp [zkcash_core.admin.MERKLE_TREE_HEIGHT] at height_post; scalar_tac
    refine WP.spec_bind (Pₘ := fun _ => True) ?_ ?_
    · unfold zkcash_core.merkle_tree.initialize_loop
      apply loop.spec_decr_nat
        (fun x : (core.ops.range.Range Usize) × (Std.Array (Std.Array U8 32#usize) 26#usize) =>
          26 - x.1.start.val)
        (fun x => x.1.start.val ≤ 26 ∧ x.1.end.val = 26)
      · rintro ⟨it, a⟩ ⟨hk, hend⟩
        dsimp only at hk hend ⊢
        unfold zkcash_core.merkle_tree.initialize_loop.body
        step
        by_cases hlt : it.start.val < it.end.val
        · rw [if_pos hlt] at o_post
          obtain ⟨rfl, hs1⟩ := o_post
          simp only
          step*
        · rw [if_neg hlt] at o_post
          obtain ⟨rfl, -⟩ := o_post
          simp
      · exact ⟨by simp, by simpa using hh⟩
    · intro _ _
      step*
  obtain ⟨⟨r, t⟩, hr, h1⟩ := (WP.spec_equiv_exists _ _).mp hspec
  simp only at h1; subst h1
  exact ⟨t, hr⟩

end Connection

namespace Connection

theorem adminInitialize_complete {H : zkcash_core.merkle_tree.Hasher Unit}
    {z : Std.Array (Std.Array U8 32#usize) 41#usize} (hzb : H.zero_bytes = ok z)
    (t0 : zkcash_core.merkle_tree.MerkleTreeAccount) (tk0 : zkcash_core.admin.TreeTokenAccount)
    (c0 : zkcash_core.admin.GlobalConfig) (auth : Pubkey) (b1 b2 b3 : U8) :
    ∃ t tk c, zkcash_core.admin.initialize H t0 tk0 c0 auth b1 b2 b3 = ok (.Ok (), t, tk, c) := by
  obtain ⟨t, ht⟩ := initTree_complete hzb t0 auth b1 zkcash_core.admin.DEFAULT_MAX_DEPOSIT_AMOUNT
  refine ⟨t, ⟨auth, b2⟩, ⟨auth, 0#u16, 25#u16, 500#u16, b3⟩, ?_⟩
  unfold zkcash_core.admin.initialize
  rw [ht]
  simp [core.result.Result.Insts.CoreOpsTry.branch]

/-- `setOD s k o dt`: `s` with account `k` given owner `o` and data `dt` (its lamports kept). -/
def setOD (s : State) (k o : Pubkey) (dt : AccountData) : State :=
  s.set k { s k with owner := o, data := dt }

@[simp] theorem setOD_lamports (s : State) (k o : Pubkey) (dt : AccountData) (x : Pubkey) :
    (setOD s k o dt x).lamports = (s x).lamports := by
  unfold setOD State.set; split_ifs with h <;> simp [h]

theorem setOD_same (s : State) (k o : Pubkey) (dt : AccountData) :
    setOD s k o dt k = { s k with owner := o, data := dt } := by simp [setOD]

theorem setOD_other (s : State) {k x : Pubkey} (o : Pubkey) (dt : AccountData) (h : x ≠ k) :
    setOD s k o dt x = s x := by simp [setOD, State.set, h]

theorem exb' {ε α β : Type} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl

/-- Anchor `init` of an address already holding at least its rent (and paid by another account):
    nothing is transferred, the account just becomes the program's. -/
theorem initAccount_funded {pid : Pubkey} {s : State} {mb : Nat → U64} {payer key : Pubkey}
    {space : Nat} {data : AccountData} (hfund : (mb space).val ≤ (s key).lamports.val)
    (hpos : 0 < (mb space).val) (hpk : payer ≠ key) :
    s.initAccount pid mb payer key space data = some (setOD s key pid data) := by
  unfold State.initAccount
  have h0 : (s key).lamports.val ≠ 0 := by omega
  have ht : max (mb space).val 1 - (s key).lamports.val = 0 := by omega
  simp only [if_neg h0, if_neg hpk, ht, if_pos]
  rfl

/-! ## Every account the program's, or a plain system account -/

/-- `Tidy d s`: every account is either the program's (owned by it, with one of its account types)
    or a plain system account (owned by the System Program, no data). The executions built here
    keep this. -/
def Tidy (d : Deployment) (s : State) : Prop :=
  ∀ k, ((s k).owner = d.programId ∧ (s k).data.isProgramData = true) ∨
    ((s k).owner = systemProgram ∧ (s k).data = .empty)

/-! ## `initialize`: the genesis and the instruction -/

/-- The genesis state for a spec run with balances `bal`: every account a plain system account
    holding its spec balance, except the pool, the config and the tree, which hold exactly their
    rent (so `initialize` transfers nothing). -/
def genesisFor (d : Deployment) (rent : Nat → U64) (bal : Spec.Pubkey → ℕ) : State := fun k =>
  { lamports := if k = d.poolAddress then rent treeTokenAccountSpace
      else if k = d.configAddress then rent globalConfigSpace
      else if k = d.treeAddress then rent treeAccountSpace
      else ⟨BitVec.ofNat 64 (bal (toPubkey k))⟩
    owner := systemProgram, data := .empty }

/-- `initialize`'s accounts, with authority `auth`. -/
def initAccounts (d : Deployment) (auth : Pubkey) : InitializeAccounts :=
  ⟨d.treeAddress, d.poolAddress, d.configAddress, auth, systemProgram⟩

/-- A transaction signed by `signers`, seeing the rent `rent`. -/
def txWith (rent : Nat → U64) (signers : List Pubkey) : TxEnv :=
  { toTxContext := ⟨signers⟩, minimumBalance := some rent }

theorem txWith_rentPositive {rent : Nat → U64} (hpos : ∀ n, 0 < (rent n).val) (signers : List Pubkey) :
    (txWith rent signers).RentPositive := by
  intro mb h n; cases h; exact hpos n

end Connection

namespace Connection

/-- Two start parameters with the same initializer have the same config: `initialize` sets the
    authorities to the initializer and every setting to its default. -/
theorem InitParams.cfg_eq {p q : Spec.InitParams} (h : p.initializer = q.initializer) :
    p.cfg = q.cfg := by
  have h1 := p.authority_init; have h2 := p.limitAuthority_init
  have h3 := q.authority_init; have h4 := q.limitAuthority_init
  have h5 := p.depositFeeRate_default; have h6 := q.depositFeeRate_default
  have h7 := p.withdrawalFeeRate_default; have h8 := q.withdrawalFeeRate_default
  have h9 := p.feeErrorMargin_default; have h10 := q.feeErrorMargin_default
  have h11 := p.maxDepositLimit_default; have h12 := q.maxDepositLimit_default
  cases hp : p.cfg; cases hq : q.cfg
  rw [hp] at h1 h2 h5 h7 h9 h11; rw [hq] at h3 h4 h6 h8 h10 h12
  simp only at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h]

theorem fromPubkey_ne {x : Spec.Pubkey} {k : Pubkey} (h : x ≠ toPubkey k) : fromPubkey x ≠ k :=
  fun e => h (by rw [← e, toPubkey_fromPubkey])

section
variable [Spec.PoseidonHashes] [Spec.Sha]

/-- **`initialize` does what the spec's `initWorld` says.** From the genesis for the run's start
    parameters, `initialize` (signed by the run's signers, with the run's initializer as
    authority) is accepted, and leaves the world `initWorld params`, every account the program's
    or plain. -/
theorem init_complete {d : Deployment} {rent : Nat → U64} {params : Spec.InitParams}
    (hpid : d.programId ≠ systemProgram) (hashes : HashesAgree d) (hpos : ∀ n, 0 < (rent n).val)
    (hdist : d.treeAddress ≠ d.poolAddress ∧ d.treeAddress ≠ d.configAddress ∧ d.poolAddress ≠ d.configAddress)
    (dep : RunOfDeployment d rent params) :
    Genesis d.programId (genesisFor d rent params.balances) ∧
    ∃ s₁, step d (genesisFor d rent params.balances) (txWith rent (params.signers.map fromPubkey))
        (.initialize (initAccounts d (fromPubkey params.initializer))) = .ok (s₁, []) ∧
      toWorld d rent s₁ = Spec.initWorld params ∧ Tidy d s₁ ∧ Initialized d s₁ := by
  set s₀ := genesisFor d rent params.balances with hs₀
  set tx := txWith rent (params.signers.map fromPubkey) with htx
  set auth := fromPubkey params.initializer with hauth
  set a := initAccounts d auth with ha
  obtain ⟨dtp, dtc, dpc⟩ := hdist
  have hgen : Genesis d.programId s₀ := fun k e => hpid (by rw [← e]; rfl)
  refine ⟨hgen, ?_⟩
  -- the initializer is none of the three accounts
  obtain ⟨np, nt, nc⟩ := params.initializer_not_created
  rw [dep.pool] at np; rw [dep.treeAccount] at nt; rw [dep.configAccount] at nc
  have ap : auth ≠ d.poolAddress := fromPubkey_ne np
  have at' : auth ≠ d.treeAddress := fromPubkey_ne nt
  have ac : auth ≠ d.configAddress := fromPubkey_ne nc
  -- the genesis balances of the three accounts
  have l0p : (s₀ d.poolAddress).lamports = rent treeTokenAccountSpace := by simp [hs₀, genesisFor]
  have l0c : (s₀ d.configAddress).lamports = rent globalConfigSpace := by
    simp [hs₀, genesisFor, Ne.symm dpc]
  have l0t : (s₀ d.treeAddress).lamports = rent treeAccountSpace := by
    simp [hs₀, genesisFor, dtp, dtc]
  -- the account checks
  have hv : InitializeAccountsValid d.toAddresses s₀ tx.toTxContext a := by
    refine ⟨⟨rfl, ?_, ?_⟩, ⟨rfl, ?_, ?_⟩, ⟨rfl, ?_, ?_⟩, ?_, rfl⟩ <;> try rfl
    exact List.mem_map_of_mem params.initializer_signed
  -- the three inits: nothing is transferred
  set s₀₁ := setOD s₀ d.treeAddress d.programId (.treeAccount zeroTree) with hs₀₁
  set s₀₂ := setOD s₀₁ d.poolAddress d.programId (.treeToken ⟨Std.Array.repeat 32#usize 0#u8, 0#u8⟩)
    with hs₀₂
  set s₁ := setOD s₀₂ d.configAddress d.programId
    (.globalConfig ⟨Std.Array.repeat 32#usize 0#u8, 0#u16, 0#u16, 0#u16, 0#u8⟩) with hs₁
  have i1 : s₀.initAccount d.programId rent auth d.treeAddress treeAccountSpace (.treeAccount zeroTree)
      = some s₀₁ := initAccount_funded (by rw [l0t]) (hpos _) at'
  have i2 : s₀₁.initAccount d.programId rent auth d.poolAddress treeTokenAccountSpace
      (.treeToken ⟨Std.Array.repeat 32#usize 0#u8, 0#u8⟩) = some s₀₂ := by
    refine initAccount_funded ?_ (hpos _) ap
    rw [hs₀₁, setOD_lamports, l0p]
  have i3 : s₀₂.initAccount d.programId rent auth d.configAddress globalConfigSpace
      (.globalConfig ⟨Std.Array.repeat 32#usize 0#u8, 0#u16, 0#u16, 0#u16, 0#u8⟩) = some s₁ := by
    refine initAccount_funded ?_ (hpos _) ac
    rw [hs₀₂, setOD_lamports, hs₀₁, setOD_lamports, l0c]
  obtain ⟨z, hzb, -⟩ := hashes.zeroBytes
  obtain ⟨tree, token, config, hres⟩ := adminInitialize_complete hzb zeroTree
    ⟨Std.Array.repeat 32#usize 0#u8, 0#u8⟩ ⟨Std.Array.repeat 32#usize 0#u8, 0#u16, 0#u16, 0#u16, 0#u8⟩
    auth (d.canonicalBump merkleTreeSeeds) (d.canonicalBump treeTokenSeeds)
    (d.canonicalBump globalConfigSeeds)
  have hadm : zkcash_core.admin.check_admin auth d.adminPubkey = ok (.Ok ()) := by
    apply checkAdmin_complete
    intro k hk
    have := params.admin_init (toPubkey k) (by rw [dep.admin, hk]; rfl)
    rw [hauth, this, fromPubkey_toPubkey]
  set s₂ := setOD s₁ d.treeAddress (s₁ d.treeAddress).owner (.treeAccount tree) with hs₂
  set s₃ := setOD s₂ d.poolAddress (s₂ d.poolAddress).owner (.treeToken token) with hs₃
  set s₄ := setOD s₃ d.configAddress (s₃ d.configAddress).owner (.globalConfig config) with hs₄
  -- lamports never change
  have hlam : ∀ k, (s₄ k).lamports = (s₀ k).lamports := by
    intro k
    simp only [hs₄, hs₃, hs₂, hs₁, hs₀₂, hs₀₁, setOD_lamports]
  have hexec : execInitialize d s₀ tx a = .ok s₄ := by
    unfold execInitialize
    rw [if_neg (not_not.mpr hv)]
    have hA : a.authority = auth := rfl
    have hT : a.treeAccount = d.treeAddress := rfl
    have hP : a.treeTokenAccount = d.poolAddress := rfl
    have hC : a.globalConfig = d.configAddress := rfl
    split
    · rename_i h; simp [htx, txWith] at h
    rename_i mb hmb
    have hmr : mb = rent := by simp [htx, txWith] at hmb; exact hmb.symm
    subst hmr
    split
    · rename_i h
      rw [hA, hT, hP, hC, i1, Option.bind_some, i2, Option.bind_some, i3] at h; cases h
    rename_i s₁' h
    rw [hA, hT, hP, hC, i1, Option.bind_some, i2, Option.bind_some, i3] at h
    cases h
    rw [hA]
    rw [show ofResult (zkcash_core.admin.check_admin auth d.adminPubkey) = .ok (.Ok ()) by
      simp [ofResult, hadm, Option.ofResult], exb']
    rw [show ofResult (zkcash_core.admin.initialize d.crypto.hasher zeroTree
        ⟨Std.Array.repeat 32#usize 0#u8, 0#u8⟩
        ⟨Std.Array.repeat 32#usize 0#u8, 0#u16, 0#u16, 0#u16, 0#u8⟩ auth
        (d.canonicalBump merkleTreeSeeds) (d.canonicalBump treeTokenSeeds)
        (d.canonicalBump globalConfigSeeds)) = .ok (.Ok (), tree, token, config) by
      simp [ofResult, hres, Option.ofResult], exb']
    unfold checkBalanced
    have : s₄.totalLamports [a.treeAccount, a.treeTokenAccount, a.globalConfig, a.authority,
        a.systemProgram] = s₀.totalLamports [a.treeAccount, a.treeTokenAccount, a.globalConfig,
        a.authority, a.systemProgram] := by
      unfold State.totalLamports; simp only [hlam]
    exact if_pos this
  have hnoNull : ∀ k, ¬ d.IsNullifierAccount s₀ k := fun k ⟨ho, _⟩ => hpid (by rw [← ho]; rfl)
  obtain ⟨hi, params', pdep, p5, p6, p7, p8, heq, -⟩ :=
    init_between ⟨dtp, dtc, dpc⟩ hpid rfl hpos hnoNull hashes.zeroBytes_agree hexec
  refine ⟨s₄, ?_, ?_, ?_, hi⟩
  · show (do let s' ← execInitialize d s₀ tx a; pure (s', [])) = _
    rw [hexec]; rfl
  · -- the world is `initWorld params`
    have hcfg : (toWorld d rent s₄).state.config = params.cfg := by
      rw [← p7]
      exact InitParams.cfg_eq (by rw [p5]; exact toPubkey_fromPubkey _)
    have hbal : (toWorld d rent s₄).balances = (Spec.initWorld params).balances := by
      funext x
      show (s₄ (fromPubkey x)).lamports.val = _
      rw [hlam]
      simp only [Spec.initWorld, Function.update_apply, hs₀, genesisFor]
      by_cases hxp : x = params.pool
      · have : fromPubkey x = d.poolAddress := by rw [hxp, dep.pool, fromPubkey_toPubkey]
        rw [if_pos this, if_pos hxp]; exact dep.rentExemptMin.symm
      have hxp' : fromPubkey x ≠ d.poolAddress := fun e => hxp (by rw [dep.pool, ← e, toPubkey_fromPubkey])
      by_cases hxc : x = params.configAccount
      · have : fromPubkey x = d.configAddress := by rw [hxc, dep.configAccount, fromPubkey_toPubkey]
        rw [if_neg hxp', if_pos this, if_neg hxp, if_pos hxc]; exact dep.configRent.symm
      have hxc' : fromPubkey x ≠ d.configAddress :=
        fun e => hxc (by rw [dep.configAccount, ← e, toPubkey_fromPubkey])
      by_cases hxt : x = params.treeAccount
      · have : fromPubkey x = d.treeAddress := by rw [hxt, dep.treeAccount, fromPubkey_toPubkey]
        rw [if_neg hxp', if_neg hxc', if_pos this, if_neg hxp, if_neg hxc, if_pos hxt]
        exact dep.treeRent.symm
      have hxt' : fromPubkey x ≠ d.treeAddress :=
        fun e => hxt (by rw [dep.treeAccount, ← e, toPubkey_fromPubkey])
      rw [if_neg hxp', if_neg hxc', if_neg hxt', if_neg hxp, if_neg hxc, if_neg hxt,
        toPubkey_fromPubkey]
      show (BitVec.ofNat 64 (params.balances x)).toNat = params.balances x
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (params.balances_fit x)
    rw [heq]
    show Spec.World.mk (Spec.State.mk Spec.initTree ∅ params'.pool params'.nullifierAddr
        (toWorld d rent s₄).state.config params'.treeAccount params'.configAccount)
        (toWorld d rent s₄).balances params'.rentExemptMin params'.nullifierRent =
      Spec.World.mk (Spec.State.mk Spec.initTree ∅ params.pool params.nullifierAddr
        params.cfg params.treeAccount params.configAccount)
        (Spec.initWorld params).balances params.rentExemptMin params.nullifierRent
    rw [hcfg, hbal, pdep.pool, pdep.nullifierAddr s₄, pdep.rentExemptMin, pdep.nullifierRent,
      pdep.treeAccount, pdep.configAccount, dep.pool, dep.nullifierAddr s₄, dep.rentExemptMin,
      dep.nullifierRent, dep.treeAccount, dep.configAccount]
  · -- every account the program's or plain
    intro k
    by_cases hkc : k = d.configAddress
    · left; subst hkc
      simp only [hs₄, setOD_same]
      refine ⟨?_, rfl⟩
      rw [hs₃, setOD_other _ _ _ (Ne.symm dpc), hs₂, setOD_other _ _ _ (Ne.symm dtc), hs₁, setOD_same]
    by_cases hkp : k = d.poolAddress
    · left; subst hkp
      simp only [hs₄, setOD_other _ _ _ dpc, hs₃, setOD_same]
      refine ⟨?_, rfl⟩
      rw [hs₂, setOD_other _ _ _ (Ne.symm dtp), hs₁, setOD_other _ _ _ dpc, hs₀₂, setOD_same]
    by_cases hkt : k = d.treeAddress
    · left; subst hkt
      simp only [hs₄, setOD_other _ _ _ dtc, hs₃, setOD_other _ _ _ dtp, hs₂, setOD_same]
      refine ⟨?_, rfl⟩
      rw [hs₁, setOD_other _ _ _ dtc, hs₀₂, setOD_other _ _ _ dtp, hs₀₁, setOD_same]
    right
    rw [hs₄, setOD_other _ _ _ hkc, hs₃, setOD_other _ _ _ hkp, hs₂, setOD_other _ _ _ hkt, hs₁,
      setOD_other _ _ _ hkc, hs₀₂, setOD_other _ _ _ hkp, hs₀₁, setOD_other _ _ _ hkt]
    exact ⟨rfl, rfl⟩

end
end Connection

namespace Connection

/-! ## Outside actions -/

/-- Two states whose accounts have the same owners and data map to the same spec state. -/
theorem toWorld_state_congr {d : Deployment} {rent : Nat → U64} {s s' : State}
    (h : ∀ k, (s' k).owner = (s k).owner ∧ (s' k).data = (s k).data) :
    (toWorld d rent s').state = (toWorld d rent s).state := by
  have hd : ∀ k, (s' k).data = (s k).data := fun k => (h k).2
  have hn : nullifierAccountsOf d s' = nullifierAccountsOf d s := by
    ext x
    rw [mem_nullifierAccountsOf, mem_nullifierAccountsOf]
    simp only [PrivacyCash.Model.Deployment.IsNullifierAccount, (h _).1, (h _).2]
  simp only [toWorld, PrivacyCash.Model.State.treeAccount, PrivacyCash.Model.State.configAccount, hd, hn]

/-- In a well-formed state, an account the program owns with one of its account types is one of
    the spec's program accounts. -/
theorem programAccount_of_owned {d : Deployment} {rent : Nat → U64} {s : State} {k : Pubkey}
    (wf : WellFormed d s) (ho : (s k).owner = d.programId) (hd : (s k).data.isProgramData = true) :
    (toWorld d rent s).state.IsProgramAccount (toPubkey k) := by
  cases hk : (s k).data with
  | empty => rw [hk] at hd; cases hd
  | foreign => rw [hk] at hd; cases hd
  | treeAccount t =>
    have := (wf.tree k t ⟨ho, hk⟩).1
    exact Or.inr (Or.inr (Or.inl (by rw [this]; rfl)))
  | treeToken p =>
    have := (wf.pool k p ⟨ho, hk⟩).1
    exact Or.inl (by rw [this]; rfl)
  | globalConfig c =>
    have := (wf.config k c ⟨ho, hk⟩).1
    exact Or.inr (Or.inr (Or.inr (by rw [this]; rfl)))
  | nullifier b =>
    refine Or.inr (Or.inl ?_)
    show toPubkey k ∈ nullifierAccountsOf d s
    rw [mem_nullifierAccountsOf, fromPubkey_toPubkey]
    exact ⟨ho, b, hk⟩

/-- **Outside actions can do every balance change the spec allows.** From a well-formed tidy
    state, for allowed new balances `b` (the config unchanged), an outside action reaches exactly
    the spec's world with these balances, and stays tidy. -/
theorem env_complete {d : Deployment} {rent : Nat → U64} {s : State}
    (wf : WellFormed d s) (tidy : Tidy d s) (b : Spec.UpdatedValuesBetweenTransacts)
    (hb : b.Allowed (toWorld d rent s)) (hcfg : b.config = (toWorld d rent s).state.config) :
    ∃ s', EnvStep d.programId s s' ∧ toWorld d rent s' = (toWorld d rent s).withUpdatedValues b ∧
      Tidy d s' := by
  let s' : State := fun k => { s k with lamports := ⟨BitVec.ofNat 64 (b.balances (toPubkey k))⟩ }
  have hlam : ∀ x, (s' (fromPubkey x)).lamports.val = b.balances x := by
    intro x
    show (BitVec.ofNat 64 (b.balances (toPubkey (fromPubkey x)))).toNat = _
    rw [BitVec.toNat_ofNat, toPubkey_fromPubkey]
    exact Nat.mod_eq_of_lt (hb.balancesFit x)
  have hod : ∀ k, (s' k).owner = (s k).owner ∧ (s' k).data = (s k).data := fun _ => ⟨rfl, rfl⟩
  refine ⟨s', fun k => ⟨fun ho => ⟨ho, rfl, ?_⟩, fun ho => ?_⟩, ?_, fun k => ?_⟩
  · -- the program's accounts only gain
    have hd : (s k).data.isProgramData = true := by
      rcases tidy k with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · exact absurd (h.symm.trans ho) (Ne.symm wf.programNotSystem)
    have hg := hb.programAccountsGain _ (programAccount_of_owned (rent := rent) wf ho hd)
    have := hlam (toPubkey k)
    rw [fromPubkey_toPubkey] at this
    rw [this]
    have hg' : s.lamports (fromPubkey (toPubkey k)) ≤ b.balances (toPubkey k) := hg
    rw [fromPubkey_toPubkey] at hg'
    exact hg'
  · -- the other accounts are plain
    show (s k).data.isProgramData = false
    rcases tidy k with ⟨h, -⟩ | ⟨-, h⟩
    · exact absurd h ho
    · rw [h]; rfl
  · -- the world
    have hst := toWorld_state_congr (d := d) (rent := rent) hod
    show Spec.World.mk _ _ _ _ = Spec.World.mk _ _ _ _
    congr 1
    · show (toWorld d rent s').state = { (toWorld d rent s).state with config := b.config }
      rw [hst, hcfg]
    · funext x; exact hlam x
  · rw [(hod k).1, (hod k).2]; exact tidy k

end Connection

namespace Connection

/-! ## Admin instructions -/

/-- No admin changes change nothing. -/
theorem reach_nil {c₁ c₂ : Spec.config} (h : Spec.ReachableByAdminChanges [] c₁ c₂) :
    c₁ = c₂ := by
  have key : ∀ chs c₁ c₂, Spec.ReachableByAdminChanges chs c₁ c₂ → chs = [] → c₁ = c₂ := by
    intro chs c₁ c₂ hr
    induction hr with
    | noChange => intro _; rfl
    | extend ch' _ _ _ => intro heq; simp at heq
  exact key _ _ _ h rfl

/-- One admin change that reaches `c₂` from `c₁` is accepted on `c₁` with result `c₂`. -/
theorem reach_single {ch : Spec.AdminChange} {c₁ c₂ : Spec.config}
    (h : Spec.ReachableByAdminChanges [ch] c₁ c₂) : ch.apply c₁ = .accepted c₂ := by
  have key : ∀ chs c₁ c₂, Spec.ReachableByAdminChanges chs c₁ c₂ → chs = [ch] →
      ch.apply c₁ = .accepted c₂ := by
    intro chs c₁ c₂ hr
    induction hr with
    | noChange => intro h; cases h
    | extend ch' hr ha _ =>
      intro heq
      rename_i chs₀ _ _ _
      have hl := congrArg List.length heq
      simp only [List.length_append, List.length_singleton, Nat.add_eq_right] at hl
      rw [List.length_eq_zero_iff] at hl
      subst hl
      simp only [List.nil_append, List.cons.injEq, and_true] at heq
      subst heq
      rw [reach_nil hr]
      exact ha
  exact key _ _ _ h rfl

theorem signers_roundtrip (l : List Spec.Pubkey) : (l.map fromPubkey).map toPubkey = l := by
  simp [List.map_map, Function.comp_def, toPubkey_fromPubkey]

/-- The deposit limit of the admin change as the code's argument. -/
def limitArg (l : ℕ) : U64 := ⟨BitVec.ofNat 64 l⟩

theorem limitArg_val {l : ℕ} (h : l < 2 ^ 64) : (limitArg l).val = l := by
  show (BitVec.ofNat 64 l).toNat = l
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- A fee setting of the admin change as the code's argument. -/
def rateArg (r : ℕ) : U16 := ⟨BitVec.ofNat 16 r⟩

theorem rateArg_val {r : ℕ} (h : r ≤ 10000) : (rateArg r).val = r := by
  show (BitVec.ofNat 16 r).toNat = r
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)

/-- The code's instruction for a spec admin change, on state `s`: `update_deposit_limit` on the
    tree, or `update_global_config` on the config, by the authority stored there. -/
def adminIx (d : Deployment) (s : State) : Spec.AdminAction → Instruction
  | .depositLimit l => .updateDepositLimit ⟨d.treeAddress, (s.treeAccount d.treeAddress).authority⟩ (limitArg l)
  | .feeSettings dr wr m => .updateGlobalConfig ⟨d.configAddress, (s.configAccount d.configAddress).authority⟩
      (some (rateArg dr)) (some (rateArg wr)) (some (rateArg m))

/-- The canonical tree, pool and config addresses with the stored canonical bumps. -/
theorem treeAddr_eq (d : Deployment) : d.treeAddress = d.createProgramAddress
    (merkleTreeSeeds ++ [d.canonicalBump merkleTreeSeeds]) := rfl
theorem configAddr_eq (d : Deployment) : d.configAddress = d.createProgramAddress
    (globalConfigSeeds ++ [d.canonicalBump globalConfigSeeds]) := rfl

end Connection

namespace Connection

/-- `update_global_config` with three settings, each at most 10000, returns. -/
theorem ugc_complete (c : zkcash_core.admin.GlobalConfig) {dr wr m : U16}
    (hd : dr.val ≤ 10000) (hw : wr.val ≤ 10000) (hm : m.val ≤ 10000) :
    zkcash_core.admin.update_global_config c (some dr) (some wr) (some m) =
      ok (.Ok (), { c with deposit_fee_rate := dr, withdrawal_fee_rate := wr, fee_error_margin := m }) := by
  have hmax : (zkcash_core.admin.MAX_BASIS_POINTS).val = 10000 := by
    simp [zkcash_core.admin.MAX_BASIS_POINTS]
  have h1 : dr ≤ zkcash_core.admin.MAX_BASIS_POINTS := by rw [UScalar.le_equiv, hmax]; exact hd
  have h2 : wr ≤ zkcash_core.admin.MAX_BASIS_POINTS := by rw [UScalar.le_equiv, hmax]; exact hw
  have h3 : m ≤ zkcash_core.admin.MAX_BASIS_POINTS := by rw [UScalar.le_equiv, hmax]; exact hm
  unfold zkcash_core.admin.update_global_config
  simp only [if_pos h1, if_pos h2, if_pos h3]

section
variable [Spec.PoseidonHashes]

omit [Spec.PoseidonHashes] in
/-- **The admin instructions can do every admin change the spec allows.** From a well-formed tidy
    initialized state, the code's instruction for an admin change the spec accepts (`adminIx`),
    signed by the change's signers, is accepted, is recorded as that change, and leaves the spec's
    world with the new config and the same balances. -/
theorem admin_complete {d : Deployment} {rent : Nat → U64} {s : State}
    (wf : WellFormed d s) (tidy : Tidy d s) (hi : Initialized d s) (ch : Spec.AdminChange)
    (c' : Spec.config) (happly : ch.apply (toWorld d rent s).state.config = .accepted c') :
    ∃ s', step d s (txWith rent (ch.signers.map fromPubkey)) (adminIx d s ch.action) = .ok (s', []) ∧
      toAdminChange d s (txWith rent (ch.signers.map fromPubkey)) (adminIx d s ch.action) = some ch ∧
      toWorld d rent s' = (toWorld d rent s).withUpdatedValues ⟨(toWorld d rent s).balances, c', []⟩ ∧
      Tidy d s' ∧ Initialized d s' := by
  obtain ⟨⟨t, ht⟩, ⟨p, hp⟩, ⟨cfg, hc⟩⟩ := hi
  have htAt : s.treeAccount d.treeAddress = t := by simp only [PrivacyCash.Model.State.treeAccount, ht.2]
  have hcAt : s.configAccount d.configAddress = cfg := by simp only [PrivacyCash.Model.State.configAccount, hc.2]
  set tx := txWith rent (ch.signers.map fromPubkey) with htx
  -- the world after a step that only rewrote one account's data
  have finish : ∀ s' : State, ∀ ix : Instruction, (∀ k, (s' k).lamports = (s k).lamports) →
      step d s tx ix = .ok (s', []) → toAdminChange d s tx ix = some ch →
      toWorld d rent s' = (toWorld d rent s).withUpdatedValues
        (recordChanges (toWorld d rent s') (toAdminChange d s tx ix).toList) →
      (recordChanges (toWorld d rent s') (toAdminChange d s tx ix).toList).Allowed (toWorld d rent s) →
      toWorld d rent s' = (toWorld d rent s).withUpdatedValues ⟨(toWorld d rent s).balances, c', []⟩ := by
    intro s' ix hlam _ hrec hw ha
    have hreach := ha.config
    rw [hrec] at hreach
    have hc' : (toWorld d rent s').state.config = c' := by
      have := reach_single hreach
      rw [happly] at this
      exact (Spec.AdminResult.accepted.inj this).symm
    have hbal : (toWorld d rent s').balances = (toWorld d rent s).balances := by
      funext x; show (s' (fromPubkey x)).lamports.val = (s (fromPubkey x)).lamports.val; rw [hlam]
    rw [hw]
    show (toWorld d rent s).withUpdatedValues ⟨(toWorld d rent s').balances,
      (toWorld d rent s').state.config, _⟩ = _
    rw [hbal, hc']; rfl
  obtain ⟨signers, act⟩ := ch
  cases act with
  | depositLimit l =>
    simp only [Spec.AdminChange.apply] at happly
    split_ifs at happly with hcond
    obtain ⟨hsig, hl⟩ := hcond
    set a : UpdateDepositLimitAccounts := ⟨d.treeAddress, t.authority⟩ with ha
    have hsig' : t.authority ∈ tx.signers := by
      have : (toWorld d rent s).state.config.limitAuthority = toPubkey t.authority := by
        simp only [toWorld, toConfig, htAt]
      rw [this] at hsig
      exact List.mem_map.mpr ⟨_, hsig, fromPubkey_toPubkey _⟩
    have hv : UpdateDepositLimitAccountsValid d.toAddresses s tx.toTxContext a t :=
      ⟨⟨ht, by rw [(wf.tree _ _ ht).2.2]; rfl, rfl⟩, hsig'⟩
    set s' := s.set d.treeAddress { s d.treeAddress with
      data := .treeAccount { t with max_deposit_amount := limitArg l } } with hs'
    have hexec : execUpdateDepositLimit d s tx a (limitArg l) = .ok s' := by
      unfold execUpdateDepositLimit
      rw [show a.treeAccount = d.treeAddress from rfl, ht.2]
      simp only
      rw [if_neg (not_not.mpr hv)]
      simp [zkcash_core.admin.update_deposit_limit, ofResult, Option.ofResult, hs']
      rfl
    have hix : adminIx d s (.depositLimit l) = .updateDepositLimit a (limitArg l) := by
      simp only [adminIx, htAt, ha]
    have hstep : step d s tx (.updateDepositLimit a (limitArg l)) = .ok (s', []) := by
      show (do let s' ← execUpdateDepositLimit d s tx a (limitArg l); pure (s', [])) = _
      rw [hexec]; rfl
    have hrec : toAdminChange d s tx (.updateDepositLimit a (limitArg l)) =
        some ⟨signers, .depositLimit l⟩ := by
      simp only [toAdminChange, htx, txWith, signers_roundtrip, limitArg_val hl]
    obtain ⟨hi', hw, hal⟩ := udl_between (rent := rent) wf ⟨⟨t, ht⟩, ⟨p, hp⟩, ⟨cfg, hc⟩⟩ hexec
    rw [hix]
    refine ⟨s', hstep, hrec, finish s' _ (fun k => set_data_lamports k) hstep hrec hw hal, ?_, hi'⟩
    intro k
    by_cases hk : k = d.treeAddress
    · subst hk; left; rw [hs', State.set_same]; exact ⟨ht.1, rfl⟩
    · rw [hs', State.set_other _ _ hk]; exact tidy k
  | feeSettings dr wr m =>
    simp only [Spec.AdminChange.apply] at happly
    split_ifs at happly with hcond
    obtain ⟨hsig, hdr, hwr, hm⟩ := hcond
    set a : UpdateGlobalConfigAccounts := ⟨d.configAddress, cfg.authority⟩ with ha
    have hsig' : cfg.authority ∈ tx.signers := by
      have : (toWorld d rent s).state.config.authority = toPubkey cfg.authority := by
        simp only [toWorld, toConfig, hcAt]
      rw [this] at hsig
      exact List.mem_map.mpr ⟨_, hsig, fromPubkey_toPubkey _⟩
    have hv : UpdateGlobalConfigAccountsValid d.toAddresses s tx.toTxContext a cfg :=
      ⟨⟨hc, by rw [(wf.config _ _ hc).2.2.2.2]; rfl, rfl⟩, hsig'⟩
    set cfg' : zkcash_core.admin.GlobalConfig := { cfg with deposit_fee_rate := rateArg dr, withdrawal_fee_rate := rateArg wr, fee_error_margin := rateArg m } with hcfg'
    set s' := s.set d.configAddress { s d.configAddress with data := .globalConfig cfg' } with hs'
    have hexec : execUpdateGlobalConfig d s tx a (some (rateArg dr)) (some (rateArg wr))
        (some (rateArg m)) = .ok s' := by
      unfold execUpdateGlobalConfig
      rw [show a.globalConfig = d.configAddress from rfl, hc.2]
      simp only
      rw [if_neg (not_not.mpr hv), ugc_complete cfg (by rw [rateArg_val hdr]; exact hdr)
        (by rw [rateArg_val hwr]; exact hwr) (by rw [rateArg_val hm]; exact hm)]
      simp [ofResult, Option.ofResult, hs']
      rfl
    have hix : adminIx d s (.feeSettings dr wr m) =
        .updateGlobalConfig a (some (rateArg dr)) (some (rateArg wr)) (some (rateArg m)) := by
      simp only [adminIx, hcAt, ha]
    have hstep : step d s tx (.updateGlobalConfig a (some (rateArg dr)) (some (rateArg wr))
        (some (rateArg m))) = .ok (s', []) := by
      unfold step; simp only; rw [hexec]; rfl
    have hrec : toAdminChange d s tx (.updateGlobalConfig a (some (rateArg dr)) (some (rateArg wr))
        (some (rateArg m))) = some ⟨signers, .feeSettings dr wr m⟩ := by
      simp only [toAdminChange, htx, txWith, signers_roundtrip, Option.getD_some, rateArg_val hdr,
        rateArg_val hwr, rateArg_val hm]
    obtain ⟨hi', hw, hal⟩ := ugc_between (rent := rent) wf ⟨⟨t, ht⟩, ⟨p, hp⟩, ⟨cfg, hc⟩⟩ hexec
    rw [hix]
    refine ⟨s', hstep, hrec, finish s' _ (fun k => set_data_lamports k) hstep hrec hw hal, ?_, hi'⟩
    intro k
    by_cases hk : k = d.configAddress
    · subst hk; left; rw [hs', State.set_same]; exact ⟨hc.1, rfl⟩
    · rw [hs', State.set_other _ _ hk]; exact tidy k

end
end Connection

namespace Connection

/-! ## Spec transactions are code transactions -/

theorem toArray_some_length {n : Usize} {bs : Spec.Bytes} {arr : Std.Array U8 n}
    (h : toArray n bs = some arr) : bs.length = n.val := by
  unfold toArray at h
  split at h
  · assumption
  · cases h

theorem toBytes_bytesToArray {n : Usize} {bs : Spec.Bytes} (h : bs.length = n.val) :
    toBytes (bytesToArray n bs).val = bs := by
  unfold bytesToArray toArray
  rw [dif_pos h]
  simp [toBytes, List.map_map, Function.comp_def]

/-- Canonical spec bytes, as a code array, are the field element they encode. -/
theorem bytesToArray_canonical {bs : Spec.Bytes} {x : Spec.F}
    (h : Spec.canonicalEncoding bs x) :
    toBytes (bytesToArray 32#usize bs).val = bs ∧ toF (bytesToArray 32#usize bs) = x := by
  have hl : bs.length = (32#usize : Usize).val := h.1
  have e := toBytes_bytesToArray hl
  refine ⟨e, ?_⟩
  rw [← e] at h
  exact ((canonicalEncoding_iff _ x).mp h).2

theorem i64_ofInt_val {z : ℤ} (h1 : -2^63 < z) (h2 : z < 2^63) :
    (⟨BitVec.ofInt 64 z⟩ : I64).val = z := by
  show (BitVec.ofInt 64 z).toInt = z
  rw [BitVec.toInt_ofInt]
  exact Int.bmod_eq_of_le (by omega) (by omega)

theorem u64_ofNat_val {n : ℕ} (h : n < 2^64) : (⟨BitVec.ofNat 64 n⟩ : U64).val = n := by
  show (BitVec.ofNat 64 n).toNat = n
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

end Connection

namespace Connection

section
variable [Spec.PoseidonHashes] [Spec.Sha]

omit [Spec.PoseidonHashes] [Spec.Sha] in
/-- **Every spec transaction is a code transaction**: `toInputs` maps `fromSpecTransact` back to it,
    when its bytes have the lengths and encodings the spec's preconditions require. -/
theorem toInputs_fromSpec (d : Deployment) (hu : Usize.max = 2^64 - 1) (inputs : Spec.TxInputs)
    (hcan : ∀ i, Spec.canonicalEncoding (inputs.pubInputBytes i)
      (Spec.Groth16.toVector inputs.pubInputs i))
    (hA : inputs.π.A.length = 64) (hB : inputs.π.B.length = 128) (hC : inputs.π.C.length = 64)
    (hrange : Spec.amountsInRange inputs.extAmt inputs.f) (hout : Spec.encOutsFit inputs)
    (hmint : inputs.mintAddr = toPubkey zkcash_core.transact.SOL_ADDRESS) :
    toInputs ⟨⟨inputs.signers.map fromPubkey⟩, fromSpecAccounts d inputs, ⟨fromSpecProof inputs,
      ⟨BitVec.ofInt 64 inputs.extAmt⟩, ⟨BitVec.ofNat 64 inputs.f⟩, toSlice inputs.encOut0,
      toSlice inputs.encOut1⟩⟩ = inputs := by
  have hp : ∀ i : Fin 7, toBytes ((publicInputs (fromSpecProof inputs))[i.val]!).val =
      inputs.pubInputBytes i ∧
      toF ((publicInputs (fromSpecProof inputs))[i.val]!) = Spec.Groth16.toVector inputs.pubInputs i := by
    intro i
    have := bytesToArray_canonical (hcan i)
    fin_cases i <;> simpa [publicInputs, fromSpecProof] using this
  obtain ⟨-, h0⟩ := hp 0; obtain ⟨-, h1⟩ := hp 1; obtain ⟨-, h2⟩ := hp 2; obtain ⟨-, h3⟩ := hp 3
  obtain ⟨-, h4⟩ := hp 4; obtain ⟨-, h5⟩ := hp 5; obtain ⟨-, h6⟩ := hp 6
  obtain ⟨r1, r2, r3⟩ := hrange
  obtain ⟨o1, o2⟩ := hout
  rcases inputs with ⟨R, pubAmt, extDataHash, k0, k1, outC0, outC1, extAmt, f, s, signers, A, t,
    encOut0, encOut1, ⟨πA, πB, πC⟩, mintAddr, pib⟩
  simp only [publicInputs, fromSpecProof] at h0 h1 h2 h3 h4 h5 h6
  simp only at o1 o2 r1 r2 r3
  simp only [toInputs, Spec.TxInputs.mk.injEq]
  refine ⟨h0, h1, h2, h3, h4, h5, h6, i64_ofInt_val r1 r2, u64_ofNat_val r3,
    toPubkey_fromPubkey _, signers_roundtrip _, toPubkey_fromPubkey _, toPubkey_fromPubkey _,
    toBytes_toSlice _ (by rw [hu]; omega), toBytes_toSlice _ (by rw [hu]; omega), ?_,
    hmint.symm, ?_⟩
  · simp only [fromSpecProof]
    rw [toBytes_bytesToArray hA, toBytes_bytesToArray hB, toBytes_bytesToArray hC]
  · funext i
    exact (hp i).1

end
end Connection

namespace Connection

/-- `transact` keeps every account the program's or plain: it creates two nullifier accounts and
    rewrites the tree's data. -/
theorem tidy_transact {d : Deployment} {s s' : State} {tx : TxEnv} {a : TransactAccounts}
    {proof : zkcash_core.transact.Proof} {ext : I64} {fee : U64} {out1 out2 : Slice U8}
    {em : List CommitmentData} (tidy : Tidy d s)
    (h : step d s tx (.transact a proof ext fee out1 out2) = .ok (s', em)) : Tidy d s' := by
  have hx : execTransact d s tx a proof ext fee out1 out2 = .ok (s', em) := h
  obtain ⟨tree, tt, config, mb, s₁, env', tree', ap, hvalid, -, hs₁, -, hs', -⟩ := execTransact_ok hx
  obtain ⟨sA, hA1, hA2⟩ := Option.bind_eq_some_iff.mp hs₁
  obtain ⟨oA, dA, kA⟩ := initAccount_ownerData hA1
  obtain ⟨o1, d1, k1⟩ := initAccount_ownerData hA2
  -- owners and data after the two inits
  have h₁ : ∀ k, ((s₁ k).owner = d.programId ∧ (s₁ k).data.isProgramData = true) ∨
      ((s₁ k).owner = systemProgram ∧ (s₁ k).data = .empty) := by
    intro k
    by_cases e1 : k = a.nullifier1
    · subst e1; left; rw [o1, d1]; exact ⟨rfl, rfl⟩
    rw [(k1 k e1).1, (k1 k e1).2]
    by_cases e0 : k = a.nullifier0
    · subst e0; left; rw [oA, dA]; exact ⟨rfl, rfl⟩
    rw [(kA k e0).1, (kA k e0).2]
    exact tidy k
  intro k
  rw [hs']
  by_cases ht : k = a.treeAccount
  · subst ht
    simp only [State.set_same]
    left
    refine ⟨?_, rfl⟩
    show (s₁ a.treeAccount).owner = d.programId
    rcases h₁ a.treeAccount with ⟨ho, -⟩ | ⟨ho, hd⟩
    · exact ho
    · exfalso
      have hT := hvalid.treeAccount.1
      by_cases e1 : a.treeAccount = a.nullifier1
      · rw [e1, o1] at ho; exact (hvalid.treeAccount.1.1 ▸ ho : _) |> fun _ => by
          rw [e1] at hd; rw [d1] at hd; cases hd
      by_cases e0 : a.treeAccount = a.nullifier0
      · rw [(k1 _ e1).2, e0, dA] at hd; cases hd
      rw [(k1 _ e1).2, (kA _ e0).2, hT.2] at hd; cases hd
  · rw [State.set_other _ _ ht]
    exact h₁ k

end Connection

namespace Connection

section
variable [Spec.PoseidonHashes] [Spec.Sha] {G1 G2 GT : Type} [AddCommGroup G1] [Inhabited G2]
  [Module Spec.F G1] [CommGroup GT]

omit [Spec.PoseidonHashes] [Spec.Sha] [Module Spec.F G1] [Inhabited G2] in
/-- The proof bytes of a valid spec proof have the points' lengths. -/
theorem proofBytes_lengths {d : Deployment} (C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT)
    (πb : Spec.Groth16.ProofBytes) (π : @Spec.Groth16.Proof (syscallGroups C))
    (h : @Spec.Groth16.ProofBytes.decode (syscallGroups C) πb = some π) :
    πb.A.length = 64 ∧ πb.B.length = 128 ∧ πb.C.length = 64 := by
  unfold Spec.Groth16.ProofBytes.decode at h
  split at h
  · rename_i A B Cp hA hB hC
    have hA' : (toArray 64#usize πb.A).bind C.decodeG1 = some A := hA
    have hB' : (toArray 128#usize πb.B).bind C.decodeG2 = some B := hB
    have hC' : (toArray 64#usize πb.C).bind C.decodeG1 = some Cp := hC
    obtain ⟨x, hx, -⟩ := Option.bind_eq_some_iff.mp hA'
    obtain ⟨y, hy, -⟩ := Option.bind_eq_some_iff.mp hB'
    obtain ⟨z, hz, -⟩ := Option.bind_eq_some_iff.mp hC'
    exact ⟨toArray_some_length hx, toArray_some_length hy, toArray_some_length hz⟩
  · cases h

/-- **One spec transaction inside a run.** From a tidy state an execution from genesis reached,
    a transaction the spec allows (not of findings L1 or A0, and without an address collision) is
    accepted as `fromSpecTransact`, and leads to exactly the spec's `transactEffects`. -/
theorem transact_run_step {d : Deployment} {rent : Nat → U64} {s₀ s : State} {evs : List Event}
    (hpid : d.programId ≠ systemProgram)
    (C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT) (laws : PairingLaws C.e)
    (hashes : HashesAgree d) (crypto : CryptoSucceeds d.crypto C) (runtime : RuntimeFacts rent)
    (hgen : Genesis d.programId s₀) (hrun : Run d s₀ evs s) (tidy : Tidy d s)
    (hi : Initialized d s) (inputs : Spec.TxInputs)
    (hpre : withSyscallSpec C in
      Spec.transactPreconditions inputs (toWorld d rent s))
    (notL1 : inputs.extAmt ≠ 0) (notA0 : inputs.π.A ≠ List.replicate 64 0)
    (nocol : ¬ AddressCollision d {fromSpecProof inputs}) :
    ∃ s' em, step d s (txWith rent (inputs.signers.map fromPubkey)) (fromSpecTransact d inputs) =
        .ok (s', em) ∧
      (withSyscallSpec C in
       toWorld d rent s' = Spec.transactEffects inputs (toWorld d rent s)) ∧ Tidy d s' := by
  withSyscallSpec C
  set tx := txWith rent (inputs.signers.map fromPubkey) with htx
  set a := fromSpecAccounts d inputs with ha
  set proof := fromSpecProof inputs with hproof
  set ext : I64 := ⟨BitVec.ofInt 64 inputs.extAmt⟩ with hext
  set fee : U64 := ⟨BitVec.ofNat 64 inputs.f⟩ with hfee
  have wf := wf_reachable hgen hrun hpid hashes
  obtain ⟨π, hdec, -⟩ := hpre.validZKP
  obtain ⟨lA, lB, lC⟩ := proofBytes_lengths C _ π hdec
  have hinputs : toInputs ⟨⟨tx.signers⟩, a, ⟨proof, ext, fee, toSlice inputs.encOut0,
      toSlice inputs.encOut1⟩⟩ = inputs :=
    toInputs_fromSpec d runtime.usize64 inputs hpre.canonicalInputs lA lB lC hpre.amountRange
      hpre.encOutLength hpre.solMint
  -- the signer is a plain account, and none of the program's
  have hsNot := hpre.signerNotPoolNotNullifiers
  have hsP : ¬ (toWorld d rent s).state.IsProgramAccount (toPubkey a.signer) := by
    have e : toPubkey a.signer = inputs.s := toPubkey_fromPubkey inputs.s
    rw [e]; exact hsNot.1
  have signerPlain : SignerIsPlain s a := by
    rcases tidy a.signer with ⟨ho, hd⟩ | ⟨ho, hd⟩
    · exact absurd (programAccount_of_owned (rent := rent) wf ho hd) hsP
    · exact ⟨ho, by rw [hd]; rfl⟩
  have hA0 : proof.proof_a.val ≠ List.replicate 64 0#u8 := by
    intro e
    apply notA0
    rw [← toBytes_bytesToArray (n := 64#usize) lA]
    show toBytes proof.proof_a.val = _
    rw [e]; simp [toBytes]
  have hL1 : ext.val ≠ 0 := by
    rw [i64_ofInt_val hpre.amountRange.1 hpre.amountRange.2.1]; exact notL1
  have hallows : Spec.transactPreconditions (toInputs ⟨⟨tx.signers⟩, a, ⟨proof, ext, fee,
      toSlice inputs.encOut0, toSlice inputs.encOut1⟩⟩) (toWorld d rent s) := by
    rw [hinputs]; exact hpre
  obtain ⟨s', em, hstep, hw⟩ := step_ok_of_match (transact_complete_square_pf ⟨_, _, hgen, hrun⟩ hpid C
    laws hashes crypto runtime (fun seeds => tidy (d.pda seeds))
    (transactDistinct_of_noCollision (Set.mem_singleton _) nocol)
    (show SameRent rent tx.minimumBalance from rfl) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ signerPlain
    hi hL1 hA0 hallows)
  rw [hinputs] at hw
  exact ⟨s', em, hstep, hw, tidy_transact tidy hstep⟩

end
end Connection

namespace Connection

/-! ## Executions and views, piece by piece -/

theorem ExecutionPath.append {d : Deployment} {s s' s'' : State} {e₁ e₂ : List Event}
    {st₁ st₂ : List State} (h₁ : ExecutionPath d s e₁ st₁ s') (h₂ : ExecutionPath d s' e₂ st₂ s'') :
    ExecutionPath d s (e₁ ++ e₂) (st₁ ++ st₂) s'' := by
  induction h₁ with
  | nil => exact h₂
  | program hs hr _ ih => exact .program hs hr (ih h₂)
  | env he _ ih => exact .env he (ih h₂)

theorem afterEvents_append {d : Deployment} {rent : Nat → U64} {s s' : State}
    {e₁ e₂ : List Event} {st₁ st₂ : List State} (h₁ : ExecutionPath d s e₁ st₁ s')
    (v : ExecutionView) :
    ExecutionView.afterEvents d rent v s (e₁ ++ e₂) (st₁ ++ st₂) =
      ExecutionView.afterEvents d rent (ExecutionView.afterEvents d rent v s e₁ st₁) s' e₂ st₂ := by
  induction h₁ generalizing v with
  | nil => rfl
  | program _ _ _ ih => exact ih _
  | env _ _ ih => exact ih _

/-- A single program step as an execution path. -/
theorem ExecutionPath.single {d : Deployment} {s s' : State} {tx : TxEnv} {ix : Instruction}
    {em : List CommitmentData} (h : step d s tx ix = .ok (s', em)) (hr : tx.RentPositive) :
    ExecutionPath d s [.program tx ix em] [s'] s' := .program h hr (.nil _)

/-- A single outside action as an execution path. -/
theorem ExecutionPath.singleEnv {d : Deployment} {s s' : State} (h : EnvStep d.programId s s') :
    ExecutionPath d s [.env] [s'] s' := .env h (.nil _)

section
variable [Spec.PoseidonHashes] [Spec.Sha]

/-- **A list of admin changes the spec allows, as admin instructions.** From a well-formed tidy
    initialized state reached from genesis, admin changes `chs` that take the spec's config to
    `c₂` are a sequence of accepted admin instructions: the view records exactly `chs`, no spec
    transaction, and the world gets the config `c₂` with the same balances. -/
theorem admin_chain {d : Deployment} {rent : Nat → U64} {s₀ : State}
    (hpid : d.programId ≠ systemProgram) (hashes : HashesAgree d) (hpos : ∀ n, 0 < (rent n).val)
    {chs : List Spec.AdminChange} {c₁ c₂ : Spec.config}
    (hr : Spec.ReachableByAdminChanges chs c₁ c₂) :
    ∀ {s : State} {pre : List Event}, Genesis d.programId s₀ → Run d s₀ pre s → Tidy d s →
      Initialized d s → (toWorld d rent s).state.config = c₁ →
      ∃ evs states s', ExecutionPath d s evs states s' ∧ Tidy d s' ∧ Initialized d s' ∧
        toWorld d rent s' = (toWorld d rent s).withUpdatedValues ⟨(toWorld d rent s).balances, c₂, []⟩ ∧
        runTxs evs = [] ∧
        ∀ v, ExecutionView.afterEvents d rent v s evs states = { v with openGap := v.openGap ++ chs } := by
  induction hr with
  | noChange c =>
    intro s pre _ _ tidy hi hc
    refine ⟨[], [], s, .nil _, tidy, hi, ?_, rfl, fun v => by cases v; simp [ExecutionView.afterEvents]⟩
    rw [← hc]; rfl
  | @extend chs c₁ c₂ c₃ ch hr' ha ih =>
    intro s pre hgen hrun tidy hi hc
    obtain ⟨evs, states, s₂, hp, tidy₂, hi₂, hw₂, hrt, hv⟩ := ih hgen hrun tidy hi hc
    have hrun₂ : Run d s₀ (pre ++ evs) s₂ := hrun.append hp.toRun
    have wf₂ := wf_reachable hgen hrun₂ hpid hashes
    have hc₂ : (toWorld d rent s₂).state.config = c₂ := by rw [hw₂]; rfl
    rw [← hc₂] at ha
    obtain ⟨s₃, hstep, hrec, hw₃, tidy₃, hi₃⟩ := admin_complete (rent := rent) wf₂ tidy₂ hi₂ ch c₃ ha
    have hp₃ := ExecutionPath.single hstep (txWith_rentPositive hpos _)
    refine ⟨evs ++ _, states ++ _, s₃, hp.append hp₃, tidy₃, hi₃, ?_, ?_, fun v => ?_⟩
    · rw [hw₃, hw₂]; rfl
    · rw [runTxs_append, hrt]
      cases ch with
      | mk sg act => cases act <;> rfl
    · rw [afterEvents_append hp, hv]
      have hix : ∀ ix, (∀ a, ix ≠ .initialize a) → (∀ a p e f o1 o2, ix ≠ .transact a p e f o1 o2) →
          ∀ (w : ExecutionView) tx em, w.afterEvent d rent s₂ (.program tx ix em) s₃ =
            { w with openGap := w.openGap ++ (toAdminChange d s₂ tx ix).toList } := by
        intro ix h1 h2 w tx em
        cases ix with
        | «initialize» a => exact absurd rfl (h1 a)
        | transact a p e f o1 o2 => exact absurd rfl (h2 a p e f o1 o2)
        | updateDepositLimit => rfl
        | updateGlobalConfig => rfl
      simp only [ExecutionView.afterEvents]
      rw [hix _ (by cases ch with | mk sg act => cases act <;> simp [adminIx])
        (by cases ch with | mk sg act => cases act <;> simp [adminIx]), hrec]
      simp

end
end Connection

namespace Connection

section
variable [Spec.PoseidonHashes] [Spec.Sha] [Spec.Groups] [AddCommGroup Spec.G1]
  [Module Spec.F Spec.G1]
  [CommGroup Spec.GT] [Spec.Pairing] [Spec.Deployment]

/-- What the spec sees of the code execution built for the first `k` transactions of run `r`. -/
def viewAt (params : Spec.InitParams) (r : Spec.Run (Spec.initWorld params)) (k : ℕ)
    (pool : Spec.Pubkey) : ExecutionView where
  init := some ⟨params.initializer, params.signers, Spec.initWorld params⟩
  closedGaps := (List.range k).map fun j => (r.updatedValues j).adminChanges
  openGap := []
  poolBeforeTx := (List.range k).map fun j => (r.updatedValues j).balances pool
  afterTx := (List.range k).map fun j => ((r.ws (j+1)).state, (r.ws (j+1)).poolBalance)

/-- The view at `k` matches the run, as `IsRunOf` requires, when `k` is the run's length. -/
theorem runMatchesView_of_viewAt {d : Deployment} {rent : Nat → U64} {s : State}
    {params : Spec.InitParams} {r : Spec.Run (Spec.initWorld params)}
    (dep : RunOfDeployment d rent params) (hw : toWorld d rent s = r.final) :
    RunMatchesView d rent (viewAt params r r.txs.length (toPubkey d.poolAddress)) r.txs s params r := by
  refine ⟨dep, ⟨_, rfl, rfl, rfl, rfl, ?_⟩, rfl,
    by simp [viewAt], ?_, by simp [viewAt], ?_, by simp [viewAt], ?_,
    Spec.UpdatedValuesBetweenTransacts.unchanged r.final,
    ⟨fun _ _ => le_rfl, fun x => by rw [← hw]; exact toWorld_fit d rent s x, .noChange _⟩, rfl, ?_⟩
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx
    obtain ⟨hp, ht, hc⟩ := hx
    simp only [Spec.initWorld, Function.update_of_ne hp, Function.update_of_ne hc,
      Function.update_of_ne ht]
  · intro j hj; simp [viewAt, List.getElem?_range hj]
  · intro j hj; simp [viewAt, List.getElem?_range hj]
  · intro j hj; simp [viewAt, List.getElem?_range hj]
  · rw [hw]; rfl

end
end Connection

namespace Connection

section
variable [Spec.PoseidonHashes] [Spec.Sha] {G1 G2 GT : Type} [AddCommGroup G1] [Inhabited G2]
  [Module Spec.F G1] [CommGroup GT]

omit [Spec.PoseidonHashes] [Spec.Sha] in
/-- The spec run's program accounts don't depend on the config. -/
theorem isProgramAccount_withConfig (st : Spec.State) (c : Spec.config) (x : Spec.Pubkey) :
    ({ st with config := c } : Spec.State).IsProgramAccount x ↔ st.IsProgramAccount x := Iff.rfl

omit [Spec.PoseidonHashes] in
/-- The spec transaction of `fromSpecTransact` is the spec transaction it came from. -/
theorem stepTxs_fromSpec {d : Deployment} {rent : Nat → U64} {s : State}
    (C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT) (h64 : Usize.max = 2^64 - 1)
    (inputs : Spec.TxInputs)
    (hpre : withSyscallSpec C in
      Spec.transactPreconditions inputs (toWorld d rent s)) :
    stepTxs (txWith rent (inputs.signers.map fromPubkey)) (fromSpecTransact d inputs) = [inputs] := by
  withSyscallSpec C
  obtain ⟨π, hdec, -⟩ := hpre.validZKP
  obtain ⟨lA, lB, lC⟩ := proofBytes_lengths C _ π hdec
  show [toInputs ⟨⟨inputs.signers.map fromPubkey⟩, _, ⟨_, _, _, _, _⟩⟩] = _
  rw [toInputs_fromSpec d h64 inputs hpre.canonicalInputs lA lB lC hpre.amountRange
    hpre.encOutLength hpre.solMint]

/-- **Completeness over runs (proof).** Every spec run of this deployment, without transactions of
    findings L1 and A0 and without address collisions, is what a code execution from genesis went
    through (`IsRunOf`). -/
theorem run_complete_pf {d : Deployment} {rent : Nat → U64}
    (hpid : d.programId ≠ systemProgram)
    (C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT) (laws : PairingLaws C.e)
    (hashes : HashesAgree d) (crypto : CryptoSucceeds d.crypto C) (runtime : RuntimeFacts rent)
    (hdist : d.treeAddress ≠ d.poolAddress ∧ d.treeAddress ≠ d.configAddress ∧ d.poolAddress ≠ d.configAddress)
    (params : Spec.InitParams)
    (r : withSyscallSpec C in
      Spec.Run (Spec.initWorld params))
    (dep : RunOfDeployment d rent params)
    (notL1 : withSyscallSpec C in
      ∀ j (h : j < r.txs.length), r.txs[j].extAmt ≠ 0)
    (notA0 : withSyscallSpec C in
      ∀ j (h : j < r.txs.length), r.txs[j].π.A ≠ List.replicate 64 0)
    (nocol : withSyscallSpec C in
      ∀ j (h : j < r.txs.length), ¬ AddressCollision d {fromSpecProof r.txs[j]}) :
    withSyscallSpec C in
    ∃ sGenesis evs states s, Genesis d.programId sGenesis ∧ ExecutionPath d sGenesis evs states s ∧
      IsRunOf d rent sGenesis evs states s params r := by
  withSyscallSpec C
  set s₀ := genesisFor d rent params.balances with hs₀
  set pool := toPubkey d.poolAddress with hpool
  obtain ⟨hgen, s₁, hinit, hw₁, tidy₁, hi₁⟩ := init_complete hpid hashes runtime.rentPositive hdist dep
  have hp₁ := ExecutionPath.single hinit (txWith_rentPositive runtime.rentPositive _)
  -- the invariant, for the first `k` transactions
  have key : ∀ k, k ≤ r.txs.length → ∃ evs states s, ExecutionPath d s₀ evs states s ∧ Tidy d s ∧
      Initialized d s ∧ toWorld d rent s = r.ws k ∧
      executionView d rent s₀ evs states = viewAt params r k pool ∧ runTxs evs = r.txs.take k := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨_, _, s₁, hp₁, tidy₁, hi₁, by rw [hw₁, r.start], ?_, rfl⟩
      simp only [executionView, ExecutionView.afterEvents, ExecutionView.afterEvent, viewAt,
        List.range_zero, List.map_nil, initAccounts, txWith, signers_roundtrip, toPubkey_fromPubkey, hw₁]
    | succ k ih =>
      intro hk
      have hk' : k < r.txs.length := by omega
      obtain ⟨evs, states, s, hp, tidy, hi, hw, hv, hrt⟩ := ih (by omega)
      have hrun : Run d s₀ evs s := hp.toRun
      -- the admin changes
      have hc : (toWorld d rent s).state.config = (r.ws k).state.config := by rw [hw]
      obtain ⟨eA, stA, sA, hpA, tidyA, hiA, hwA, hrtA, hvA⟩ :=
        admin_chain (rent := rent) hpid hashes runtime.rentPositive (r.allowed k hk').config hgen hrun tidy hi hc
      have hrunA : Run d s₀ (evs ++ eA) sA := hrun.append hpA.toRun
      have wfA := wf_reachable hgen hrunA hpid hashes
      -- the balances
      set b : Spec.UpdatedValuesBetweenTransacts :=
        ⟨(r.updatedValues k).balances, (r.updatedValues k).config, []⟩ with hb
      have hwA' : toWorld d rent sA = (r.ws k).withUpdatedValues
          ⟨(r.ws k).balances, (r.updatedValues k).config, []⟩ := by rw [hwA, hw]
      have hbA : b.Allowed (toWorld d rent sA) := by
        refine ⟨fun x hx => ?_, (r.allowed k hk').balancesFit, ?_⟩
        · rw [hwA'] at hx ⊢
          exact (r.allowed k hk').programAccountsGain x hx
        · rw [hwA']; exact .noChange _
      obtain ⟨sE, henv, hwE, tidyE⟩ := env_complete (rent := rent) wfA tidyA b hbA (by rw [hwA']; rfl)
      have hpE := ExecutionPath.singleEnv henv
      have hrunE : Run d s₀ (evs ++ eA ++ [.env]) sE := hrunA.append (.env henv (.nil _))
      have hiE : Initialized d sE := env_initialized henv hiA
      have hwE' : toWorld d rent sE = (r.ws k).withUpdatedValues (r.updatedValues k) := by
        rw [hwE, hwA']; rfl
      -- the transaction
      have hpre := (r.step k hk').1
      rw [← hwE'] at hpre
      obtain ⟨s', em, hstep, hw', tidy'⟩ := transact_run_step hpid C laws hashes crypto runtime hgen
        hrunE tidyE hiE r.txs[k] hpre (notL1 k hk') (notA0 k hk') (nocol k hk')
      have hp' := ExecutionPath.single hstep (txWith_rentPositive runtime.rentPositive _)
      have hws : toWorld d rent s' = r.ws (k+1) := by
        rw [hw', hwE']; exact (agrees_eq (r.step k hk').2).symm
      refine ⟨evs ++ eA ++ [.env] ++ _, states ++ stA ++ [sE] ++ _, s',
        ((hp.append hpA).append hpE).append hp', tidy', ?_, hws, ?_, ?_⟩
      · exact transact_initialized (wf_reachable hgen hrunE hpid hashes) hiE hstep
      · -- the view
        unfold executionView
        rw [afterEvents_append ((hp.append hpA).append hpE), afterEvents_append (hp.append hpA),
          afterEvents_append hp]
        unfold executionView at hv
        rw [hv, hvA]
        have hpE' : sE.lamports d.poolAddress = (r.updatedValues k).balances pool := by
          have := congrArg (fun w => w.balances pool) hwE'
          simp only [Spec.World.withUpdatedValues] at this
          rw [← this]; show _ = sE.lamports (fromPubkey (toPubkey d.poolAddress))
          rw [fromPubkey_toPubkey]
        have hp's : s'.lamports d.poolAddress = (r.ws (k+1)).poolBalance := by
          rw [← hws]; show _ = s'.lamports (fromPubkey (toPubkey d.poolAddress))
          rw [fromPubkey_toPubkey]
        simp only [ExecutionView.afterEvents, ExecutionView.afterEvent, fromSpecTransact, viewAt,
          List.range_succ, List.map_append, List.map_cons, List.map_nil, List.nil_append, hpE',
          hp's, hws]
      · -- the transactions
        rw [runTxs_append, runTxs_append, runTxs_append, hrt, hrtA]
        simp only [runTxs, List.append_nil]
        rw [stepTxs_fromSpec (s := sE) C runtime.usize64 r.txs[k] hpre]
        rw [List.take_add_one, List.getElem?_eq_getElem hk']
        rfl
    -- the end
  obtain ⟨evs, states, s, hp, -, -, hw, hv, hrt⟩ := key r.txs.length le_rfl
  refine ⟨s₀, evs, states, s, hgen, hp, ?_⟩
  apply isRunOf_of_view hp.length_eq
  unfold IsRunOfView
  rw [hv, hrt, List.take_length]
  exact runMatchesView_of_viewAt dep hw

/-- `run_complete_pf` with the exclusions as `run_complete_except_L1_A0` states them: over the
    run's transactions, and no address collision (`AddressCollision`). -/
theorem run_complete_of {d : Deployment} {rent : Nat → U64} {params : Spec.InitParams}
    (hpid : d.programId ≠ systemProgram)
    (C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT) (laws : PairingLaws C.e)
    (hashes : HashesAgree d) (crypto : CryptoSucceeds d.crypto C) (runtime : RuntimeFacts rent)
    (r : SpecRun C params) (dep : RunOfDeployment d rent params)
    (notL1 : ∀ tx ∈ r.txs, tx.extAmt ≠ 0) (notA0 : ∀ tx ∈ r.txs, tx.π.A ≠ List.replicate 64 0)
    (hc : ¬ AddressCollision d (fromSpecProof '' {tx | tx ∈ r.txs})) :
    withSyscallSpec C in
    ∃ sGenesis evs states s, Genesis d.programId sGenesis ∧ ExecutionPath d sGenesis evs states s ∧
      IsRunOf d rent sGenesis evs states s params r :=
  run_complete_pf hpid C laws hashes crypto runtime
    (singleton_pdas_distinct_of _ _ _ (distinct_of_noCollision (fun h => hc (Or.inl h))))
    params r dep (fun _ hj => notL1 _ (List.getElem_mem hj)) (fun _ hj => notA0 _ (List.getElem_mem hj))
    (fun _ hj h => hc (by
      rcases h with h | ⟨p, rfl, h⟩
      exacts [Or.inl h, Or.inr ⟨_, ⟨_, List.getElem_mem hj, rfl⟩, h⟩]))

end
end Connection

