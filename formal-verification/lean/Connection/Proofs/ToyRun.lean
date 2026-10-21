import Connection.Proofs.Toy
open Aeneas Aeneas.Std Result PrivacyCash.Model

/-! # A toy execution (not for review)

Genesis, `initialize`, one deposit, in the toy deployment of `Connection/Proofs/Toy.lean`, with
a toy PDA derivation (`toyCPA`) that separates the addresses the run uses. Every hypothesis of
the main result `transact_connection_main` holds for the deposit (`toy_execution`). -/

namespace Connection.Toy
open zkcash_core
attribute [local instance] toyPoseidon toySpecSha

theorem initLoop_complete (iter : core.ops.range.Range Usize)
    (a : Std.Array (Std.Array U8 32#usize) 26#usize) (z : Std.Array (Std.Array U8 32#usize) 41#usize)
    (hk : iter.start.val ≤ 26) (hend : iter.end.val = 26) :
    merkle_tree.initialize_loop iter a z ⦃ _ => True ⦄ := by
  unfold merkle_tree.initialize_loop
  apply loop.spec_decr_nat
    (fun x : (core.ops.range.Range Usize) × (Std.Array (Std.Array U8 32#usize) 26#usize) => 26 - x.1.start.val)
    (fun x => x.1.start.val ≤ 26 ∧ x.1.end.val = 26)
  · rintro ⟨it, a⟩ ⟨hk, hend⟩
    dsimp only at hk hend ⊢
    unfold merkle_tree.initialize_loop.body
    step*
    all_goals (
      have ho : o = some i := ‹_›
      have hlt : it.start.val < it.end.val := by
        by_contra hc; rw [if_neg hc] at o_post; rw [o_post.1] at ho; cases ho
      rw [if_pos hlt] at o_post
      obtain ⟨hoo, hs1⟩ := o_post
      rw [hoo] at ho; cases ho)
    · simp; omega
    · simp; omega
    · refine ⟨by omega, by rw [o_post1]; exact hend, by omega⟩
  · exact ⟨hk, hend⟩

theorem toy_admin_initialize (tk0 : admin.TreeTokenAccount) (c0 : admin.GlobalConfig) (auth : Pubkey) (b1 b2 b3 : U8) :
    admin.initialize toyHasher zeroTree tk0 c0 auth b1 b2 b3 ⦃ r => r.1 = .Ok () ∧
      r.2.1.root_history.val[0]! = one32 ∧ r.2.1.next_index = 0#u64 ∧ r.2.1.bump = b1 ∧
      r.2.1.max_deposit_amount = admin.DEFAULT_MAX_DEPOSIT_AMOUNT ∧ r.2.2.1.bump = b2 ∧
      r.2.2.2.bump = b3 ⦄ := by
  unfold admin.initialize admin.init_tree merkle_tree.initialize
  step*
  have hx : x.val = 26 := by rw [x_post]; simp [admin.MERKLE_TREE_HEIGHT]
  bstep (rfl : toyHasher.zero_bytes = ok toyZ)
  step with initLoop_complete { start := 0#usize, «end» := x } _ _ (by simp) (by simpa using hx)
  step*
  rename_i hroot _ _ _
  rw [x_post, Std.Array.set_val_eq, getElem!_pos _ _ (by simp)]
  simp only [List.getElem_set]
  rw [hroot]
  have := toyZ_succ 25 (by omega)
  rw [getElem!_pos _ _ (by simp)] at this
  simpa [hx] using this

/-! ## The toy deployment and genesis -/

/-- Toy PDA derivation: distinguishes the inputs the toy run uses (length, the slot byte of the
    nullifier seeds, the last nullifier byte); marked 170 in byte 0 so it never is a `pk n`. -/
def toyCPA (l : List U8) : Pubkey :=
  Std.Array.make 32#usize ([170#u8, ⟨BitVec.ofNat 8 l.length⟩, l.getD 9 0#u8, l.getD 41 0#u8] ++
    List.replicate 28 0#u8) (by simp)

def toyD : Deployment :=
  { programId := pk 100#u8, createProgramAddress := toyCPA, canonicalBump := fun _ => 255#u8,
    crypto := toyCrypto, adminPubkey := none }

def toyS0 : State := fun k =>
  if k = pk 1#u8 then { lamports := 1000#u64, owner := systemProgram, data := .empty } else Account.default

def toyTx : TxEnv := { signers := [pk 1#u8], minimumBalance := some (fun _ => 1#u64) }

def toyInitA : InitializeAccounts :=
  { treeAccount := toyD.pda merkleTreeSeeds, treeTokenAccount := toyD.pda treeTokenSeeds,
    globalConfig := toyD.pda globalConfigSeeds, authority := pk 1#u8, systemProgram := systemProgram }

theorem toyGenesis : Genesis toyD.programId toyS0 := by
  intro k; unfold toyS0; split <;> decide

/-- Anchor's `init` succeeds on an empty address, paid by a system account that can pay. -/
theorem initAccount_some {pid : Pubkey} {s : State} {mb : Nat → U64} {payer key : Pubkey}
    {space : Nat} {data : AccountData} (hzero : (s key).lamports.val = 0)
    (ho : (s payer).owner = systemProgram) (hd : (s payer).data.isEmpty)
    (hle : (mb space).val ≤ (s payer).lamports.val) (hne : payer ≠ key)
    (hfit : (mb space).val ≤ U64.max) :
    ∃ s', s.initAccount pid mb payer key space data = some s' := by
  unfold State.initAccount
  simp only [hzero, if_true]
  unfold State.systemTransfer systemTransferBalances
  rw [if_pos ⟨ho, hd, hle⟩]
  simp only
  rw [if_pos (by simp only [State.balances, setBalance, if_neg (Ne.symm hne), hzero]; omega)]
  exact ⟨_, rfl⟩


def treeA : Pubkey := toyD.pda merkleTreeSeeds
def tokenA : Pubkey := toyD.pda treeTokenSeeds
def configA : Pubkey := toyD.pda globalConfigSeeds

theorem addr_facts : treeA ≠ pk 1#u8 ∧ tokenA ≠ pk 1#u8 ∧ configA ≠ pk 1#u8 ∧ treeA ≠ tokenA ∧ treeA ≠ configA ∧
    tokenA ≠ configA ∧ treeA ≠ systemProgram := by
  unfold treeA tokenA configA
  decide +kernel


theorem exb {ε α β : Type} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl

/-- Anchor's `init` with rent 1, on an empty address: what it does to every account. -/
theorem init_step {s : State} {pid payer key : Pubkey} {space : Nat} {data : AccountData}
    (hzero : (s key).lamports.val = 0) (ho : (s payer).owner = systemProgram)
    (hd : (s payer).data.isEmpty) (hle : 1 ≤ (s payer).lamports.val) (hne : payer ≠ key) :
    ∃ s', s.initAccount pid (fun _ => 1#u64) payer key space data = some s' ∧
      (s' payer).owner = (s payer).owner ∧ (s' payer).data = (s payer).data ∧
      (s' payer).lamports.val = (s payer).lamports.val - 1 ∧
      (s' key).owner = pid ∧ (s' key).data = data ∧ (s' key).lamports.val = 1 ∧
      (∀ k, k ≠ payer → k ≠ key → s' k = s k) ∧
      (fun k => (s' k).lamports.val) = moveN (fun k => (s k).lamports.val) payer key 1 := by
  obtain ⟨s', h⟩ := initAccount_some (pid := pid) (mb := fun _ => 1#u64) (space := space) (data := data) hzero ho hd
    (by simpa using hle) hne (by scalar_tac)
  obtain ⟨-, -, -, hl, hok, hdk, hk⟩ := initAccount_empty hzero h
  have hv : (1#u64 : U64).val = 1 := by simp
  refine ⟨s', h, (hk payer hne).1, (hk payer hne).2, ?_, hok, hdk, ?_, fun k h1 h2 => ?_,
    by rw [hl, hv]⟩
  · rw [show (s' payer).lamports.val = _ from congrFun hl payer]
    simp only [moveN, Function.update_of_ne hne, Function.update_self, hv]
  · rw [show (s' key).lamports.val = _ from congrFun hl key]
    simp only [moveN, Function.update_self, Function.update_of_ne (Ne.symm hne), hzero, hv]
  · have hlk : (s' k).lamports.val = (s k).lamports.val := by
      rw [show (s' k).lamports.val = _ from congrFun hl k, moveN_other _ _ h1 h2]
    obtain ⟨e1, e2⟩ := hk k h2
    have hlk' : (s' k).lamports = (s k).lamports := UScalar.eq_of_val_eq hlk
    cases hs : s' k; cases hs' : s k
    rw [hs] at e1 e2 hlk'; rw [hs'] at e1 e2 hlk'
    simp only at e1 e2 hlk'
    rw [e1, e2, hlk']

theorem set_data_lamports (s : State) (key : Pubkey) (dt : AccountData) :
    (fun k => ((s.set key { s key with data := dt }) k).lamports.val) = fun k => (s k).lamports.val := by
  funext k; by_cases h : k = key
  · subst h; simp
  · simp [State.set, h]

/-- `initialize` succeeds when each of its parts does. -/
theorem execInitialize_ok_of {d : Deployment} {s : State} {tx : TxEnv} {a : InitializeAccounts}
    {mb : Nat → U64} {s₁ : State} {tree : merkle_tree.MerkleTreeAccount}
    {token : admin.TreeTokenAccount} {config : admin.GlobalConfig}
    (hv : InitializeAccountsValid d.toAddresses s tx.toTxContext a)
    (hmb : tx.minimumBalance = some mb)
    (hinit : ((s.initAccount d.programId mb a.authority a.treeAccount treeAccountSpace
        (.treeAccount zeroTree)).bind
      (·.initAccount d.programId mb a.authority a.treeTokenAccount treeTokenAccountSpace
        (.treeToken ⟨Std.Array.repeat 32#usize 0#u8, 0#u8⟩))).bind
      (·.initAccount d.programId mb a.authority a.globalConfig globalConfigSpace
        (.globalConfig ⟨Std.Array.repeat 32#usize 0#u8, 0#u16, 0#u16, 0#u16, 0#u8⟩)) = some s₁)
    (hadm : admin.check_admin a.authority d.adminPubkey = ok (.Ok ()))
    (hres : admin.initialize d.crypto.hasher zeroTree ⟨Std.Array.repeat 32#usize 0#u8, 0#u8⟩
        ⟨Std.Array.repeat 32#usize 0#u8, 0#u16, 0#u16, 0#u16, 0#u8⟩ a.authority
        (d.canonicalBump merkleTreeSeeds) (d.canonicalBump treeTokenSeeds)
        (d.canonicalBump globalConfigSeeds) = ok (.Ok (), tree, token, config))
    (hTL : TL [a.treeAccount, a.treeTokenAccount, a.globalConfig, a.authority, a.systemProgram]
        (fun k => (s₁ k).lamports.val)
      = TL [a.treeAccount, a.treeTokenAccount, a.globalConfig, a.authority, a.systemProgram]
        (fun k => (s k).lamports.val)) :
    execInitialize d s tx a = .ok (((s₁.set a.treeAccount { s₁ a.treeAccount with data := .treeAccount tree }).set
        a.treeTokenAccount { (s₁.set a.treeAccount { s₁ a.treeAccount with data := .treeAccount tree })
          a.treeTokenAccount with data := .treeToken token }).set a.globalConfig
        { ((s₁.set a.treeAccount { s₁ a.treeAccount with data := .treeAccount tree }).set
          a.treeTokenAccount { (s₁.set a.treeAccount { s₁ a.treeAccount with data := .treeAccount tree })
            a.treeTokenAccount with data := .treeToken token }) a.globalConfig with
          data := .globalConfig config }) := by
  unfold execInitialize
  rw [if_neg (not_not.mpr hv)]
  split
  · rename_i h; rw [hmb] at h; cases h
  rename_i mb' h; rw [hmb] at h; cases h
  split
  · rename_i h; rw [hinit] at h; cases h
  rename_i s₁' h; rw [hinit] at h; cases h
  rw [show ofResult (admin.check_admin a.authority d.adminPubkey) = .ok (.Ok ()) by
    simp [ofResult, hadm, Option.ofResult], exb]
  rw [show ofResult (admin.initialize d.crypto.hasher zeroTree ⟨Std.Array.repeat 32#usize 0#u8, 0#u8⟩
        ⟨Std.Array.repeat 32#usize 0#u8, 0#u16, 0#u16, 0#u16, 0#u8⟩ a.authority
        (d.canonicalBump merkleTreeSeeds) (d.canonicalBump treeTokenSeeds)
        (d.canonicalBump globalConfigSeeds)) = .ok (.Ok (), tree, token, config) by
    simp [ofResult, hres, Option.ofResult], exb]
  unfold checkBalanced
  have hbal := totalLamports_eq (((s₁.set a.treeAccount { s₁ a.treeAccount with data := .treeAccount tree }).set
        a.treeTokenAccount { (s₁.set a.treeAccount { s₁ a.treeAccount with data := .treeAccount tree })
          a.treeTokenAccount with data := .treeToken token }).set a.globalConfig
        { ((s₁.set a.treeAccount { s₁ a.treeAccount with data := .treeAccount tree }).set
          a.treeTokenAccount { (s₁.set a.treeAccount { s₁ a.treeAccount with data := .treeAccount tree })
            a.treeTokenAccount with data := .treeToken token }) a.globalConfig with
          data := .globalConfig config }) [a.treeAccount, a.treeTokenAccount, a.globalConfig, a.authority, a.systemProgram]
  rw [set_data_lamports, set_data_lamports, set_data_lamports, hTL, ← totalLamports_eq] at hbal
  have hbal' := (Nat.cast_inj (R := ℤ)).mp hbal
  simp only [hbal']
  rfl


theorem acct_eq (x : Account) (l : U64) (o : Pubkey) (d : AccountData) (hl : x.lamports.val = l.val)
    (ho : x.owner = o) (hd : x.data = d) : x = ⟨l, o, d⟩ := by
  cases x; simp only at hl ho hd; rw [UScalar.eq_of_val_eq hl, ho, hd]

/-- **`initialize` succeeds** on the toy genesis, with this state afterwards. -/
theorem toy_init_ok : ∃ (s₁ : State) (tree : merkle_tree.MerkleTreeAccount)
    (token : admin.TreeTokenAccount) (config : admin.GlobalConfig),
    execInitialize toyD toyS0 toyTx toyInitA = .ok s₁ ∧
    s₁ treeA = ⟨1#u64, toyD.programId, .treeAccount tree⟩ ∧
    s₁ tokenA = ⟨1#u64, toyD.programId, .treeToken token⟩ ∧
    s₁ configA = ⟨1#u64, toyD.programId, .globalConfig config⟩ ∧
    s₁ (pk 1#u8) = ⟨997#u64, systemProgram, .empty⟩ ∧
    (∀ k, k ≠ treeA → k ≠ tokenA → k ≠ configA → k ≠ pk 1#u8 → s₁ k = toyS0 k) ∧
    TreeShape tree ∧ (∀ j : Fin 100, Canonical tree.root_history.val[j.val]!) ∧
    (∀ j : Fin 26, Canonical tree.subtrees.val[j.val]!) ∧ tree.root_history.val[0]! = one32 ∧
    tree.next_index = 0#u64 ∧ tree.bump = 255#u8 ∧
    tree.max_deposit_amount = admin.DEFAULT_MAX_DEPOSIT_AMOUNT ∧ token.bump = 255#u8 ∧
    config.bump = 255#u8 ∧ config.deposit_fee_rate.val = 0 ∧ config.withdrawal_fee_rate.val = 25 ∧
    config.fee_error_margin.val = 500 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := addr_facts
  have hvalid : InitializeAccountsValid toyD.toAddresses toyS0 toyTx.toTxContext toyInitA := by
    refine ⟨⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, by simp [toyInitA, toyTx], rfl⟩ <;>
      (unfold Initializable toyInitA; decide +kernel)
  obtain ⟨sA, hA, oA, dA, lA, oAk, dAk, lAk, kA, mA⟩ := init_step (pid := toyD.programId)
    (space := treeAccountSpace) (data := .treeAccount zeroTree) (s := toyS0)
    (payer := toyInitA.authority) (key := toyInitA.treeAccount)
    (by unfold toyS0 toyInitA; decide +kernel) (by unfold toyS0 toyInitA; decide +kernel)
    (by unfold toyS0 toyInitA; decide +kernel) (by unfold toyS0 toyInitA; decide +kernel) h1.symm
  have lA' : (sA toyInitA.authority).lamports.val = 999 := by
    rw [lA]; unfold toyS0 toyInitA; decide +kernel
  obtain ⟨sB, hB, oB, dB, lB, oBk, dBk, lBk, kB, mB⟩ := init_step (pid := toyD.programId)
    (space := treeTokenAccountSpace) (data := .treeToken ⟨Std.Array.repeat 32#usize 0#u8, 0#u8⟩)
    (s := sA) (payer := toyInitA.authority) (key := toyInitA.treeTokenAccount)
    (by rw [kA toyInitA.treeTokenAccount h2 (Ne.symm h4)]; unfold toyS0 toyInitA; decide +kernel)
    (by rw [oA]; unfold toyS0 toyInitA; decide +kernel)
    (by rw [dA]; unfold toyS0 toyInitA; decide +kernel) (by rw [lA']; omega) h2.symm
  have lB' : (sB toyInitA.authority).lamports.val = 998 := by rw [lB, lA']
  obtain ⟨sC, hC, oC, dC, lC, oCk, dCk, lCk, kC, mC⟩ := init_step (pid := toyD.programId)
    (space := globalConfigSpace)
    (data := .globalConfig ⟨Std.Array.repeat 32#usize 0#u8, 0#u16, 0#u16, 0#u16, 0#u8⟩)
    (s := sB) (payer := toyInitA.authority) (key := toyInitA.globalConfig)
    (by rw [kB toyInitA.globalConfig h3 (Ne.symm h6), kA toyInitA.globalConfig h3 (Ne.symm h5)]; unfold toyS0 toyInitA; decide +kernel)
    (by rw [oB, oA]; unfold toyS0 toyInitA; decide +kernel)
    (by rw [dB, dA]; unfold toyS0 toyInitA; decide +kernel) (by rw [lB']; omega) h3.symm
  obtain ⟨⟨r, tree, token, config⟩, hres, hr, hT0, hTn, hTb, hTm, hkb, hcb⟩ := (WP.spec_equiv_exists _ _).mp
    (toy_admin_initialize ⟨Std.Array.repeat 32#usize 0#u8, 0#u8⟩
      ⟨Std.Array.repeat 32#usize 0#u8, 0#u16, 0#u16, 0#u16, 0#u8⟩ toyInitA.authority
      (toyD.canonicalBump merkleTreeSeeds) (toyD.canonicalBump treeTokenSeeds)
      (toyD.canonicalBump globalConfigSeeds))
  simp only at hr; subst hr
  obtain ⟨hshape, hdr, hwr, hmr, hroots, hsubs⟩ :=
    adminInitialize_ok toyHashesAgree.zeroBytesCanonical zeroTree_history zeroTree_subtrees hres
  set K := [toyInitA.treeAccount, toyInitA.treeTokenAccount, toyInitA.globalConfig,
      toyInitA.authority, toyInitA.systemProgram] with hK
  have t3 : TL K (fun k => (sC k).lamports.val) = TL K (fun k => (sB k).lamports.val) := by
    rw [mC]; exact TL_moveN (by simp [hK]) (by simp [hK]) _ (by show 1 ≤ (sB toyInitA.authority).lamports.val; omega)
  have t2 : TL K (fun k => (sB k).lamports.val) = TL K (fun k => (sA k).lamports.val) := by
    rw [mB]; exact TL_moveN (by simp [hK]) (by simp [hK]) _ (by show 1 ≤ (sA toyInitA.authority).lamports.val; omega)
  have t1 : TL K (fun k => (sA k).lamports.val) = TL K (fun k => (toyS0 k).lamports.val) := by
    rw [mA]; exact TL_moveN (by simp [hK]) (by simp [hK]) _
      (by show 1 ≤ (toyS0 toyInitA.authority).lamports.val; unfold toyS0 toyInitA; decide +kernel)
  have hTL : TL K (fun k => (sC k).lamports.val) = TL K (fun k => (toyS0 k).lamports.val) := by
    rw [t3, t2, t1]
  have n1 : treeA ≠ toyInitA.treeTokenAccount := h4
  have n2 : treeA ≠ toyInitA.globalConfig := h5
  have n3 : tokenA ≠ toyInitA.globalConfig := h6
  have n4 : tokenA ≠ toyInitA.treeAccount := Ne.symm h4
  have n5 : configA ≠ toyInitA.treeAccount := Ne.symm h5
  have n6 : configA ≠ toyInitA.treeTokenAccount := Ne.symm h6
  have n7 : pk 1#u8 ≠ toyInitA.treeAccount := Ne.symm h1
  have n8 : pk 1#u8 ≠ toyInitA.treeTokenAccount := Ne.symm h2
  have n9 : pk 1#u8 ≠ toyInitA.globalConfig := Ne.symm h3
  have m1 : toyInitA.treeTokenAccount ≠ toyInitA.treeAccount := Ne.symm h4
  have m2 : toyInitA.globalConfig ≠ toyInitA.treeTokenAccount := Ne.symm h6
  have m3 : toyInitA.globalConfig ≠ toyInitA.treeAccount := Ne.symm h5
  have p1 : treeA = toyInitA.treeAccount := rfl
  have p2 : tokenA = toyInitA.treeTokenAccount := rfl
  have p3 : configA = toyInitA.globalConfig := rfl
  refine ⟨_, tree, token, config,
    execInitialize_ok_of hvalid rfl (by rw [hA, Option.bind_some, hB, Option.bind_some, hC]) rfl hres hTL,
    ?_, ?_, ?_, ?_, ?_, hshape, hroots, hsubs, hT0, hTn, hTb, hTm, hkb, hcb, hdr, hwr, hmr⟩
  · -- the tree account
    simp only [State.set, if_neg n2, if_neg n1, if_pos p1]
    rw [kC toyInitA.treeAccount h1 h5, kB toyInitA.treeAccount h1 h4]
    exact acct_eq _ _ _ _ (by rw [lAk]; rfl) oAk rfl
  · -- the pool
    simp only [State.set, if_neg n3, if_pos p2, if_neg m1]
    rw [kC toyInitA.treeTokenAccount h2 h6]
    exact acct_eq _ _ _ _ (by rw [lBk]; rfl) oBk rfl
  · -- the config
    simp only [State.set, if_pos p3, if_neg m2, if_neg m3]
    exact acct_eq _ _ _ _ (by rw [lCk]; rfl) oCk rfl
  · -- the authority
    simp only [State.set, if_neg n9, if_neg n8, if_neg n7]
    have hl : (sC toyInitA.authority).lamports.val = 997 := by rw [lC, lB']
    have ho : (sC toyInitA.authority).owner = systemProgram :=
      (oC.trans (oB.trans oA)).trans (by unfold toyS0 toyInitA; decide +kernel)
    have hd : (sC toyInitA.authority).data = .empty :=
      (dC.trans (dB.trans dA)).trans (by unfold toyS0 toyInitA; decide +kernel)
    exact acct_eq _ _ _ _ (hl.trans (by simp)) ho hd
  · intro k e1 e2 e3 e4
    have f1 : k ≠ toyInitA.treeAccount := e1
    have f2 : k ≠ toyInitA.treeTokenAccount := e2
    have f3 : k ≠ toyInitA.globalConfig := e3
    simp only [State.set, if_neg f1, if_neg f2, if_neg f3]
    rw [kC k e4 e3, kB k e4 e2, kA k e4 e1]


theorem withBalances_set_lamports (s : State) (b : Pubkey → U64) (key : Pubkey) (dt : AccountData) :
    (fun k => (((s.withBalances b).set key { (s.withBalances b) key with data := dt }) k).lamports.val)
      = fun k => (b k).val := by
  funext k; by_cases h : k = key
  · subst h; simp [State.withBalances]
  · simp [State.set, h, State.withBalances]

/-- `transact` succeeds when each of its parts does. -/
theorem execTransact_ok_of {d : Deployment} {s : State} {tx : TxEnv} {a : TransactAccounts}
    {proof : transact.Proof} {ext : I64} {fee : U64} {out1 out2 : Slice U8}
    {tree : merkle_tree.MerkleTreeAccount} {tt : admin.TreeTokenAccount} {config : admin.GlobalConfig}
    {mb : Nat → U64} {s₁ : State} {ap : transact.Appended} {env' : SolEnv}
    {tree' : merkle_tree.MerkleTreeAccount}
    (htd : (s a.treeAccount).data = .treeAccount tree) (hpd : (s a.treeTokenAccount).data = .treeToken tt)
    (hcd : (s a.globalConfig).data = .globalConfig config)
    (hv : TransactAccountsValid d.toAddresses s tx.toTxContext a proof.input_nullifiers.val[0]!
      proof.input_nullifiers.val[1]! tree tt config)
    (hmb : tx.minimumBalance = some mb)
    (hinit : (s.initAccount d.programId mb a.signer a.nullifier0 nullifierAccountSpace (.nullifier 0#u8)).bind
        (·.initAccount d.programId mb a.signer a.nullifier1 nullifierAccountSpace (.nullifier 0#u8)) = some s₁)
    (hh : transact.transact d.crypto.hasher arkFr d.crypto.sha256 d.crypto.proofVerifier solRuntime
        { accounts := s₁, balances := s₁.balances, signer := a.signer,
          treeToken := a.treeTokenAccount, recipient := a.recipient,
          feeRecipient := a.feeRecipientAccount, rentExemptMinimum := some (mb treeTokenAccountSpace) }
        tree config proof ext fee a.recipient a.feeRecipientAccount out1 out2 = ok (.Ok ap, env', tree'))
    (hTL : TL [a.treeAccount, a.nullifier0, a.nullifier1, a.nullifier2, a.nullifier3, a.treeTokenAccount,
          a.globalConfig, a.recipient, a.feeRecipientAccount, a.signer, a.systemProgram]
        (fun k => (env'.balances k).val)
      = TL [a.treeAccount, a.nullifier0, a.nullifier1, a.nullifier2, a.nullifier3, a.treeTokenAccount,
          a.globalConfig, a.recipient, a.feeRecipientAccount, a.signer, a.systemProgram]
        (fun k => (s k).lamports.val)) :
    ∃ s' events, execTransact d s tx a proof ext fee out1 out2 = .ok (s', events) := by
  unfold execTransact
  split
  rotate_left
  · rename_i hn; exact (hn _ _ _ htd hpd hcd).elim
  rename_i tree0 tt0 config0 e1 e2 e3
  rw [htd] at e1; rw [hpd] at e2; rw [hcd] at e3
  cases e1; cases e2; cases e3
  rw [if_neg (not_not.mpr hv)]
  split
  · rename_i h; rw [hmb] at h; cases h
  rename_i mb' h; rw [hmb] at h; cases h
  split
  · rename_i h; rw [hinit] at h; cases h
  rename_i s₁' h; rw [hinit] at h; cases h
  dsimp only
  rw [show ofResult (transact.transact d.crypto.hasher arkFr d.crypto.sha256 d.crypto.proofVerifier solRuntime
        { accounts := s₁, balances := s₁.balances, signer := a.signer,
          treeToken := a.treeTokenAccount, recipient := a.recipient,
          feeRecipient := a.feeRecipientAccount, rentExemptMinimum := some (mb treeTokenAccountSpace) }
        tree config proof ext fee a.recipient a.feeRecipientAccount out1 out2) = .ok (.Ok ap, env', tree') by
    simp [ofResult, hh, Option.ofResult], exb]
  unfold checkBalanced
  have hbal := totalLamports_eq ((s₁.withBalances env'.balances).set a.treeAccount
    { (s₁.withBalances env'.balances) a.treeAccount with data := .treeAccount tree' })
    [a.treeAccount, a.nullifier0, a.nullifier1, a.nullifier2, a.nullifier3, a.treeTokenAccount,
      a.globalConfig, a.recipient, a.feeRecipientAccount, a.signer, a.systemProgram]
  rw [withBalances_set_lamports, hTL, ← totalLamports_eq] at hbal
  have hbal' := (Nat.cast_inj (R := ℤ)).mp hbal
  simp only [hbal']
  exact ⟨_, _, rfl⟩


/-! ## The deposit -/

def nf0A : Pubkey := toyD.pda (nullifier0Seeds zeros32)
def nf1A : Pubkey := toyD.pda (nullifier1Seeds one32)
def nf2A : Pubkey := toyD.pda (nullifier0Seeds one32)
def nf3A : Pubkey := toyD.pda (nullifier1Seeds zeros32)

def depA : TransactAccounts :=
  { treeAccount := treeA, nullifier0 := nf0A, nullifier1 := nf1A, nullifier2 := nf2A,
    nullifier3 := nf3A, treeTokenAccount := tokenA, globalConfig := configA,
    recipient := pk 3#u8, feeRecipientAccount := pk 4#u8, signer := pk 1#u8,
    systemProgram := systemProgram }

def depProof : transact.Proof := toyProof verifying_key.VERIFYING_KEY.vk_alpha_g1 one32

/-- The addresses the deposit uses are distinct where it matters. -/
theorem dep_addr : nf0A ≠ treeA ∧ nf0A ≠ tokenA ∧ nf0A ≠ configA ∧ nf0A ≠ pk 1#u8 ∧
    nf1A ≠ treeA ∧ nf1A ≠ tokenA ∧ nf1A ≠ configA ∧ nf1A ≠ pk 1#u8 ∧ nf0A ≠ nf1A ∧
    nf2A ≠ treeA ∧ nf2A ≠ tokenA ∧ nf2A ≠ configA ∧ nf2A ≠ pk 1#u8 ∧
    nf3A ≠ treeA ∧ nf3A ≠ tokenA ∧ nf3A ≠ configA ∧ nf3A ≠ pk 1#u8 ∧
    pk 3#u8 ≠ treeA ∧ pk 3#u8 ≠ tokenA ∧ pk 3#u8 ≠ configA ∧
    pk 4#u8 ≠ treeA ∧ pk 4#u8 ≠ tokenA ∧ pk 4#u8 ≠ configA ∧
    pk 3#u8 ≠ nf0A ∧ pk 3#u8 ≠ nf1A ∧ pk 4#u8 ≠ nf0A ∧ pk 4#u8 ≠ nf1A ∧
    tokenA ≠ pk 1#u8 ∧ pk 1#u8 ≠ systemProgram := by
  unfold nf0A nf1A nf2A nf3A treeA tokenA configA
  decide +kernel

unseal verifying_key.VERIFYING_KEY in
theorem alpha_ne_zeros : verifying_key.VERIFYING_KEY.vk_alpha_g1.val ≠ List.replicate 64 0#u8 := by
  decide +kernel


/-- The deposit's spec preconditions, from the handler's view after the two nullifier `init`s. -/
theorem dep_pre (s₂ : State) (tree : merkle_tree.MerkleTreeAccount) (config : admin.GlobalConfig)
    (hT0 : tree.root_history.val[0]! = one32) (hTn : tree.next_index = 0#u64)
    (hTm : tree.max_deposit_amount = admin.DEFAULT_MAX_DEPOSIT_AMOUNT)
    (hdr : config.deposit_fee_rate.val = 0)
    (hsigB : (s₂ (pk 1#u8)).lamports.val = 995) (hpoolB : (s₂ tokenA).lamports.val = 1) :
    HandlerPre Unit Unit Unit toyCrypto toyC toyLaws depA s₂ 1#u64 tree config ∅ depProof 1#i64 0#u64
      emptySlice emptySlice := by
  unfold HandlerPre
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hTP, -⟩ := dep_addr
  have hdec := decode_toInputs toyC depProof depA 1#i64 0#u64 emptySlice emptySlice
    toy_alpha_decodes rfl toy_zeros_decodes
  have hk0 : depProof.input_nullifiers.val[0]! = zeros32 := rfl
  have hk1 : depProof.input_nullifiers.val[1]! = one32 := rfl
  have h10 : (1 : LeanSpec.F) ≠ 0 := by decide
  have he : (toInputs depA depProof 1#i64 0#u64 emptySlice emptySlice).extAmt = 1 := by simp [toInputs]
  have hf : (toInputs depA depProof 1#i64 0#u64 emptySlice emptySlice).f = 0 := by simp [toInputs]
  refine @LeanSpec.transactPreconditions.mk _ (syscallGroups toyC) (inferInstanceAs (AddCommGroup Unit))
    (inferInstanceAs (Module LeanSpec.F Unit)) (inferInstanceAs (AddCommGroup Unit))
    (inferInstanceAs (Module LeanSpec.F Unit)) (inferInstanceAs (CommGroup Unit))
    (syscallPairing toyC toyLaws) (@LeanSpec.Deployment.mk (syscallGroups toyC) (programKey toyC)) _ _
    ?_ ?_ ?_ ?_ ⟨_, hdec, rfl⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · show LeanSpec.rootBytesKnown (toTree tree) (toBytes one32.val)
    rw [rootBytesKnown_iff]
    refine ⟨canonical_one32, ⟨⟨0, ?_⟩, by rw [toF_one32]; exact h10⟩⟩
    show toF (tree.root_history.val[0]!) = toF one32
    rw [hT0]
  · show (LeanSpec.natOfLE (List.replicate 32 0) : LeanSpec.F) = toF zeros32
    rw [toF_zeros32]; rfl
  · unfold LeanSpec.feeSufficient; rw [he, hf]; simp [handlerWorld, toConfig, hdr]
  · unfold LeanSpec.pubAmtConsistent; rw [he, hf]
    refine ⟨fun _ => by omega, ?_⟩
    show toF one32 = _; rw [toF_one32]; simp
  · simp [LeanSpec.nullifiersFresh, handlerWorld]
  · show toF _ ≠ toF _
    rw [hk0, hk1, toF_zeros32, toF_one32]; exact h10.symm
  · intro _; rw [he]; show (1 : ℤ) ≤ (tree.max_deposit_amount.val : ℤ)
    rw [hTm]; simp [admin.DEFAULT_MAX_DEPOSIT_AMOUNT]
  · unfold LeanSpec.poolSolvent; rw [he, hf]
    exact ⟨fun h => by omega, fun h => by omega⟩
  · unfold LeanSpec.signerSolvent; rw [he]
    show (s₂ (fromPubkey (toPubkey depA.signer))).lamports.val ≥ 2 * 0 + _
    rw [fromPubkey_toPubkey]; show (s₂ (pk 1#u8)).lamports.val ≥ _; rw [hsigB]; simp
  · show tree.next_index.val ≤ 2 ^ 26 - 2; rw [hTn]; simp
  · unfold LeanSpec.amountsInRange; rw [he, hf]; norm_num
  · simp [LeanSpec.encOutsFit, toInputs, emptySlice, toBytes]
  · refine ⟨fun e => (Ne.symm hTP) (toPubkey_inj e), fun h => ?_, fun h => ?_⟩
    · rw [he] at h; omega
    · rw [hf] at h; omega
  · intro i
    show LeanSpec.canonicalEncoding (toBytes ((publicInputs _)[i.val]!).val) _
    rw [canonicalEncoding_iff]
    fin_cases i
    · exact ⟨canonical_one32, rfl⟩
    · exact ⟨canonical_one32, rfl⟩
    · exact ⟨canonical_zeros32, rfl⟩
    · exact ⟨canonical_zeros32, rfl⟩
    · exact ⟨canonical_one32, rfl⟩
    · exact ⟨canonical_zeros32, rfl⟩
    · exact ⟨canonical_zeros32, rfl⟩
  · refine ⟨fun k hk => ?_, fun _ => ?_⟩
    · -- only the pool is credited, and it holds 1 lamport
      have hpool : (handlerWorld depA s₂ 1#u64 tree config ∅).state.pool = toPubkey tokenA := rfl
      have hnr : (handlerWorld depA s₂ 1#u64 tree config ∅).nullifierRent = 0 := rfl
      by_cases hkp : k = toPubkey tokenA
      · subst hkp
        have hb : (handlerWorld depA s₂ 1#u64 tree config ∅).balances (toPubkey tokenA) = 1 := by
          show (s₂ (fromPubkey (toPubkey tokenA))).lamports.val = 1
          rw [fromPubkey_toPubkey, hpoolB]
        rw [hb]
        unfold LeanSpec.balanceDelta
        rw [he, hf, hpool, hnr]
        split_ifs <;> norm_num
      · exfalso
        unfold LeanSpec.balanceDelta at hk
        rw [he, hf, hpool, hnr, if_neg hkp] at hk
        split_ifs at hk <;> omega
    · show ((handlerWorld depA s₂ 1#u64 tree config ∅).balances (toPubkey tokenA) : ℤ) + _ < _
      rw [he]
      show ((s₂ (fromPubkey (toPubkey tokenA))).lamports.val : ℤ) + 1 < _
      rw [fromPubkey_toPubkey, hpoolB]; norm_num


/-- **The deposit is accepted by `step`**, from the state after `initialize`. -/
theorem toy_deposit_ok (s₁ : State) (tree : merkle_tree.MerkleTreeAccount)
    (token : admin.TreeTokenAccount) (config : admin.GlobalConfig)
    (hT : s₁ treeA = ⟨1#u64, toyD.programId, .treeAccount tree⟩)
    (hK : s₁ tokenA = ⟨1#u64, toyD.programId, .treeToken token⟩)
    (hC : s₁ configA = ⟨1#u64, toyD.programId, .globalConfig config⟩)
    (hP : s₁ (pk 1#u8) = ⟨997#u64, systemProgram, .empty⟩)
    (hO : ∀ k, k ≠ treeA → k ≠ tokenA → k ≠ configA → k ≠ pk 1#u8 → s₁ k = toyS0 k)
    (hshape : TreeShape tree) (hroots : ∀ j : Fin 100, Canonical tree.root_history.val[j.val]!)
    (hsubs : ∀ j : Fin 26, Canonical tree.subtrees.val[j.val]!) (hT0 : tree.root_history.val[0]! = one32)
    (hTn : tree.next_index = 0#u64) (hTb : tree.bump = 255#u8)
    (hTm : tree.max_deposit_amount = admin.DEFAULT_MAX_DEPOSIT_AMOUNT) (hkb : token.bump = 255#u8)
    (hcb : config.bump = 255#u8) (hdr : config.deposit_fee_rate.val = 0)
    (hwr : config.withdrawal_fee_rate.val = 25) (hmr : config.fee_error_margin.val = 500) :
    ∃ s' events, step toyD s₁ toyTx (.transact depA depProof 1#i64 0#u64 emptySlice emptySlice)
      = .ok (s', events) := by
  obtain ⟨a01, a02, a03, a04, a11, a12, a13, a14, a0n1, a21, a22, a23, a24, a31, a32, a33, a34,
    -, -, -, -, -, -, -, -, -, -, hTP, -⟩ := dep_addr
  have hPs : s₁ depA.signer = ⟨997#u64, systemProgram, .empty⟩ := hP
  -- the two nullifier inits, paid by the signer
  have z0 : (s₁ depA.nullifier0).lamports.val = 0 := by
    rw [show s₁ depA.nullifier0 = toyS0 nf0A from hO nf0A a01 a02 a03 a04]; unfold toyS0; decide +kernel
  obtain ⟨sA, hA, oA, dA, lA, -, -, -, kA, mA⟩ := init_step (pid := toyD.programId)
    (space := nullifierAccountSpace) (data := .nullifier 0#u8) (s := s₁) (payer := depA.signer)
    (key := depA.nullifier0) z0 (by rw [hPs]) (by rw [hPs]; rfl) (by rw [hPs]; decide) (Ne.symm a04)
  have z1 : (sA depA.nullifier1).lamports.val = 0 := by
    rw [kA depA.nullifier1 a14 (Ne.symm a0n1), show s₁ depA.nullifier1 = toyS0 nf1A from hO nf1A a11 a12 a13 a14]
    unfold toyS0; decide +kernel
  have lA' : (sA depA.signer).lamports.val = 996 := by rw [lA, hPs]; rfl
  obtain ⟨sB, hB, oB, dB, lB, -, -, -, kB, mB⟩ := init_step (pid := toyD.programId)
    (space := nullifierAccountSpace) (data := .nullifier 0#u8) (s := sA) (payer := depA.signer)
    (key := depA.nullifier1) z1 (by rw [oA, hPs]) (by rw [dA, hPs]; rfl) (by rw [lA']; omega) (Ne.symm a14)
  have lB' : (sB depA.signer).lamports.val = 995 := by rw [lB, lA']
  have hpoolB : (sB tokenA).lamports.val = 1 := by
    rw [show sB tokenA = s₁ tokenA from (kB tokenA hTP (Ne.symm a12)).trans (kA tokenA hTP (Ne.symm a02)), hK]; rfl
  -- the handler
  obtain ⟨ap, env', tree', hh⟩ := handler_ok_exists toyCrypto toyC toyLaws toyHashesAgree toyHashesSucceed
    toySyscalls toyKey depA sB 1#u64 tree config ∅ depProof 1#i64 0#u64 emptySlice emptySlice hshape hroots
    hsubs (by omega) (by omega) (by omega)
    ⟨by rw [oB, oA, hPs], by rw [dB, dA, hPs]; rfl⟩ toyFit (by simp) alpha_ne_zeros
    (dep_pre sB tree config hT0 hTn hTm hdr lB' hpoolB)
  -- lamports are conserved
  have hok := handler_ok toyCrypto _ _ _ _ _ _ _ _ _ _ _ _ _ hh
  obtain ⟨v', -, hdep, -, -⟩ := hok.rent
  have hpos : (1#i64 : I64).val > 0 := by simp
  have he : (fun k => (env'.balances k).val) = payN (moveN (fun k => (sB k).lamports.val) depA.signer
      depA.treeTokenAccount (1#i64 : I64).val.natAbs) depA.treeTokenAccount depA.feeRecipientAccount
      (0#u64 : U64).val := (hdep hpos).2.2.2.2
  set K := [depA.treeAccount, depA.nullifier0, depA.nullifier1, depA.nullifier2, depA.nullifier3,
    depA.treeTokenAccount, depA.globalConfig, depA.recipient, depA.feeRecipientAccount, depA.signer,
    depA.systemProgram] with hK'
  have hTL : TL K (fun k => (env'.balances k).val) = TL K (fun k => (s₁ k).lamports.val) := by
    rw [he, show (0#u64 : U64).val = 0 by simp, payN_zero,
      TL_moveN (by simp [hK']) (by simp [hK']) _ (by show _ ≤ (sB depA.signer).lamports.val; rw [lB']; simp),
      mB, TL_moveN (by simp [hK']) (by simp [hK']) _ (by show 1 ≤ (sA depA.signer).lamports.val; omega),
      mA, TL_moveN (by simp [hK']) (by simp [hK']) _ (by show 1 ≤ (s₁ depA.signer).lamports.val; rw [hPs]; decide)]
  -- the account checks
  have hv : TransactAccountsValid toyD.toAddresses s₁ toyTx.toTxContext depA depProof.input_nullifiers.val[0]!
      depProof.input_nullifiers.val[1]! tree token config := by
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨⟨?_, ?_⟩, ?_⟩, ⟨⟨?_, ?_⟩, ?_⟩,
      by simp [depA, toyTx], rfl⟩
    · show (s₁ treeA).owner = _; rw [hT]
    · show (s₁ treeA).data = _; rw [hT]
    · rw [hTb]; rfl
    · show Initializable s₁ nf0A; unfold Initializable; rw [hO nf0A a01 a02 a03 a04]; unfold toyS0; decide +kernel
    · show Initializable s₁ nf1A; unfold Initializable; rw [hO nf1A a11 a12 a13 a14]; unfold toyS0; decide +kernel
    · show IsSystemAccount s₁ nf2A; unfold IsSystemAccount; rw [hO nf2A a21 a22 a23 a24]; unfold toyS0; decide +kernel
    · show IsSystemAccount s₁ nf3A; unfold IsSystemAccount; rw [hO nf3A a31 a32 a33 a34]; unfold toyS0; decide +kernel
    · show (s₁ tokenA).owner = _; rw [hK]
    · show (s₁ tokenA).data = _; rw [hK]
    · rw [hkb]; rfl
    · show (s₁ configA).owner = _; rw [hC]
    · show (s₁ configA).data = _; rw [hC]
    · rw [hcb]; rfl
  exact execTransact_ok_of (by show (s₁ treeA).data = _; rw [hT]) (by show (s₁ tokenA).data = _; rw [hK])
    (by show (s₁ configA).data = _; rw [hC]) hv rfl (by rw [hA, Option.bind_some, hB]) hh hTL


/-! ## The whole toy execution: every hypothesis of the main result holds -/

def toyRent : Nat → U64 := fun _ => 1#u64

theorem toy_execution :
    ∃ (s : State) (s' : State) (evs : List Event) (events : List CommitmentData),
      Genesis toyD.programId toyS0 ∧ Run toyD toyS0 evs s ∧ toyD.programId ≠ systemProgram ∧
      step toyD s toyTx (.transact depA depProof 1#i64 0#u64 emptySlice emptySlice) = .ok (s', events) ∧
      HashesAgree toyD.crypto ∧ SolanaFacts toyRent emptySlice emptySlice ∧ CryptoFacts toyD depProof ∧
      OutsideSpecDetail toyD toyRent s toyTx depA depProof := by
  obtain ⟨s₁, tree, token, config, hinit, hT, hK, hC, hP, hO, hshape, hroots, hsubs, hT0, hTn, hTb, hTm,
    hkb, hcb, hdr, hwr, hmr⟩ := toy_init_ok
  obtain ⟨s', events, hstep⟩ := toy_deposit_ok s₁ tree token config hT hK hC hP hO hshape hroots hsubs hT0
    hTn hTb hTm hkb hcb hdr hwr hmr
  obtain ⟨a01, a02, a03, a04, a11, a12, a13, a14, a0n1, -, -, -, -, -, -, -, -, p3T, p3K, p3C, p4T, p4K, p4C,
    p30, p31, p40, p41, -, -⟩ := dep_addr
  have hinitStep : step toyD toyS0 toyTx (.initialize toyInitA) = .ok (s₁, []) := by
    show (do let s' ← execInitialize toyD toyS0 toyTx toyInitA; pure (s', [])) = _
    rw [hinit]; rfl
  have p1 : pk 3#u8 ≠ pk 1#u8 := pk_ne (by decide)
  have p2 : pk 4#u8 ≠ pk 1#u8 := pk_ne (by decide)
  refine ⟨s₁, s', [.program toyTx (.initialize toyInitA) []], events, toyGenesis,
    .program hinitStep (.nil _), by unfold toyD; decide +kernel, hstep, toyHashesAgree,
    ⟨by simp [toyRent], toyFit⟩, ⟨?_, ?_⟩, ⟨rfl, ?_, ?_⟩⟩
  · show zeros32 ≠ one32; decide +kernel
  · intro x hx y hy hxy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rfl
    · exact absurd hxy a0n1
    · exact absurd hxy.symm a0n1
    · rfl
  · refine ⟨?_, ?_⟩
    · show (s₁ nf0A).lamports.val = 0; rw [hO nf0A a01 a02 a03 a04]; unfold toyS0; decide +kernel
    · show (s₁ nf1A).lamports.val = 0; rw [hO nf1A a11 a12 a13 a14]; unfold toyS0; decide +kernel
  · refine ⟨fun b h => ?_, fun b h => ?_, p30, p31, p40, p41⟩
    · rw [show s₁ depA.recipient = toyS0 (pk 3#u8) from hO _ p3T p3K p3C p1] at h
      unfold toyS0 at h; rw [if_neg p1] at h; cases h
    · rw [show s₁ depA.feeRecipientAccount = toyS0 (pk 4#u8) from hO _ p4T p4K p4C p2] at h
      unfold toyS0 at h; rw [if_neg p2] at h; cases h

end Connection.Toy