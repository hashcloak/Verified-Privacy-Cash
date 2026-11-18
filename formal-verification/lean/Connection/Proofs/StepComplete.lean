import Connection.Proofs.HandlerComplete
import Connection.Proofs.Transact
import Connection.Proofs.WellFormed
import Spec.Statements
open Aeneas Aeneas.Std Result PrivacyCash.Model

/-! # Proofs: `transact` accepted through Anchor's `init`s and the runtime

NOT FOR REVIEW: the proof of `transact_complete_except_L1_A0`
(`Connection/ConnectionTheorems.lean`), which G3a and G3b for the code use. If the spec's
preconditions hold in a reachable state, Anchor's account checks pass, and its `init`s, the
handler and the runtime's lamport check succeed: `step` returns `ok`. -/

namespace Connection


/-! ## What Anchor's two `init`s do to the state -/

/-- The payer of an `init` pays at most the rent, also when the address is pre-funded. -/
theorem initAccount_payer_ge {pid : Pubkey} {s s' : State} {mb : Nat → U64} {payer key : Pubkey}
    {space : Nat} {data : AccountData} (hne : payer ≠ key)
    (h : s.initAccount pid mb payer key space data = some s') :
    (s payer).lamports.val ≤ (s' payer).lamports.val + (mb space).val := by
  by_cases hz : (s key).lamports.val = 0
  · obtain ⟨_, _, _, hlam, _⟩ := initAccount_empty hz h
    have := congrFun hlam payer
    simp only [moveN, Function.update_of_ne hne, Function.update_self] at this
    omega
  unfold State.initAccount at h
  simp only [hz, if_false, hne, Option.map_eq_some_iff] at h
  obtain ⟨s₂, hf, rfl⟩ := h
  have hset : ((s₂.set key { s₂ key with owner := pid, data := data }) payer).lamports = (s₂ payer).lamports := by
    simp [State.set, hne]
  rw [hset]
  split at hf
  · cases hf; omega
  · rename_i ht
    cases hb : systemTransferBalances s s.balances payer key
        ⟨BitVec.ofNat 64 ((max (mb space).val 1) - (s key).lamports.val)⟩ with
    | none => simp [State.systemTransfer, hb] at hf
    | some b =>
    simp only [State.systemTransfer, hb, Option.map_some, Option.some.injEq] at hf
    subst hf
    obtain ⟨_, _, hle, hv⟩ := stb_spec hb
    have h1 := congrFun hv payer
    simp only [moveN, Function.update_of_ne hne, Function.update_self] at h1
    have h2 : (s.withBalances b payer).lamports.val = (b payer).val := by simp [State.withBalances]
    have h3 : ((⟨BitVec.ofNat 64 ((max (mb space).val 1) - (s key).lamports.val)⟩ : U64)).val
        ≤ (max (mb space).val 1) - (s key).lamports.val := by
      show (BitVec.ofNat 64 _).toNat ≤ _
      rw [BitVec.toNat_ofNat]; exact Nat.mod_le _ _
    have h5 : (s.balances payer).val = (s payer).lamports.val := rfl
    omega

/-- The two `init`s of a `transact`: the signer pays at most the two rents, its owner and data
    don't change, and every account but the signer and the two new ones keeps its lamports. -/
theorem after_inits {pid : Pubkey} {s s₁ : State} {mb : Nat → U64} {signer n0 n1 : Pubkey}
    {space : Nat} {data : AccountData} (hs0 : signer ≠ n0) (hs1 : signer ≠ n1)
    (h : (s.initAccount pid mb signer n0 space data).bind
      (·.initAccount pid mb signer n1 space data) = some s₁) :
    (s₁ signer).owner = (s signer).owner ∧ (s₁ signer).data = (s signer).data ∧
    (s signer).lamports.val ≤ (s₁ signer).lamports.val + 2 * (mb space).val ∧
    (s₁ signer).lamports.val ≤ (s signer).lamports.val ∧
    ∀ k, k ≠ signer → k ≠ n0 → k ≠ n1 → (s₁ k).lamports.val = (s k).lamports.val := by
  obtain ⟨sA, hA1, hA2⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨top0, _, _, _, _, hlamA, _, _, hotherA⟩ := initAccount_spec hs0 hA1
  obtain ⟨top1, _, _, _, _, hlam1, _, _, hother1⟩ := initAccount_spec hs1 hA2
  have g0 := initAccount_payer_ge hs0 hA1
  have g1 := initAccount_payer_ge hs1 hA2
  have l0 := congrFun hlamA signer
  have l1 := congrFun hlam1 signer
  simp only [moveN, Function.update_of_ne hs0, Function.update_self] at l0
  simp only [moveN, Function.update_of_ne hs1, Function.update_self] at l1
  refine ⟨?_, ?_, by omega, by omega, fun k hk h0 h1 => ?_⟩
  · exact (hother1 _ hs1).1.trans (hotherA _ hs0).1
  · exact (hother1 _ hs1).2.trans (hotherA _ hs0).2
  · have e1 := congrFun hlam1 k
    have e0 := congrFun hlamA k
    rw [moveN_other _ _ hk h1] at e1
    rw [moveN_other _ _ hk h0] at e0
    exact e1.trans e0

/-! ## Reaching the handler -/

/-- `ReachedHandler d rent s tx a proof tree tt config s₁`: Anchor's checks passed on `s` and
    its two `init`s gave `s₁`, as in `execTransact`. Not proved to happen: this is the premise
    that marks what the theorem does not cover. -/
structure ReachedHandler (d : Deployment) (rent : Nat → U64) (s : State) (tx : TxEnv)
    (a : TransactAccounts) (proof : zkcash_core.transact.Proof)
    (tree : zkcash_core.merkle_tree.MerkleTreeAccount) (tt : zkcash_core.admin.TreeTokenAccount)
    (config : zkcash_core.admin.GlobalConfig) (s₁ : State) : Prop where
  accounts : TransactAccountsValid d.toAddresses s tx.toTxContext a proof.input_nullifiers.val[0]!
    proof.input_nullifiers.val[1]! tree tt config
  rentFixed : tx.minimumBalance = some rent
  inits : (s.initAccount d.programId rent a.signer a.nullifier0 nullifierAccountSpace (.nullifier 0#u8)).bind
    (·.initAccount d.programId rent a.signer a.nullifier1 nullifierAccountSpace (.nullifier 0#u8)) = some s₁

section
variable [Spec.PoseidonHashes] [Spec.Sha] [Spec.Groups] [AddCommGroup Spec.G1]
  [Module Spec.F Spec.G1]
  [CommGroup Spec.GT] [Spec.Pairing] [Spec.Deployment]

omit [Spec.PoseidonHashes] [Spec.Sha] [Spec.Groups] [AddCommGroup Spec.G1]
  [Module Spec.F Spec.G1] [CommGroup Spec.GT] [Spec.Pairing]
  [Spec.Deployment] in
/-- A world `H` whose balances are those of `W` after the rent step, with no rent of its own and
    the same pool: every account ends where it ends from `W`. -/
theorem balanceDelta_after_rent (inputs : Spec.TxInputs) (W H : Spec.World)
    (hb : H.balances = (Spec.nullifierRentEffects inputs W).balances)
    (hp : H.state.pool = W.state.pool) (hr : H.nullifierRent = 0)
    (hSolv : W.nullifierTopUp inputs 0 + W.nullifierTopUp inputs 1 ≤ W.balances inputs.s)
    (hs0 : inputs.s ≠ W.state.newNullifierAccount inputs 0)
    (hs1 : inputs.s ≠ W.state.newNullifierAccount inputs 1)
    (h01 : W.state.newNullifierAccount inputs 0 ≠ W.state.newNullifierAccount inputs 1)
    (x : Spec.Pubkey) :
    (H.balances x : ℤ) + Spec.balanceDelta inputs H x
      = W.balances x + Spec.balanceDelta inputs W x := by
  rw [hb, Spec.nullifierRentEffects_balances inputs W hSolv hs0 hs1 h01 x,
    balanceDelta_noRent inputs H hr, hp]
  unfold Spec.balanceDelta
  push_cast
  ring

omit [Spec.PoseidonHashes] in
/-- The spec's preconditions in the code's world give them in the world the handler sees. -/
theorem preconditions_at_handler
    {d : Deployment} {rent : Nat → U64} {s s₁ : State} {tx : TxEnv}
    {a : TransactAccounts} {proof : zkcash_core.transact.Proof} {ext : I64} {fee : U64}
    {out1 out2 : Slice U8} {tree : zkcash_core.merkle_tree.MerkleTreeAccount}
    {tt : zkcash_core.admin.TreeTokenAccount} {config : zkcash_core.admin.GlobalConfig}
    (wf : WellFormed d s)
    (reached : ReachedHandler d rent s tx a proof tree tt config s₁)
    (hnr : 0 < (rent nullifierAccountSpace).val)
    (pre : Spec.transactPreconditions (toInputs ⟨⟨tx.signers⟩, a, ⟨proof, ext, fee, out1, out2⟩⟩) (toWorld d rent s)) :
    Spec.transactPreconditions (toInputs ⟨⟨tx.signers⟩, a, ⟨proof, ext, fee, out1, out2⟩⟩)
      (handlerWorld a s₁ (rent treeTokenAccountSpace) tree config (nullifierAccountsOf d s)
        (nullifierAddrOf d)) := by
  set inputs := toInputs ⟨⟨tx.signers⟩, a, ⟨proof, ext, fee, out1, out2⟩⟩ with hinputs
  set W := toWorld d rent s with hWdef
  set H := handlerWorld a s₁ (rent treeTokenAccountSpace) tree config (nullifierAccountsOf d s)
    (nullifierAddrOf d) with hHdef
  have hvalid := reached.accounts
  obtain ⟨htreeAddr, _⟩ := wf.tree _ _ hvalid.treeAccount.1
  have hpoolAddr := (wf.pool _ _ hvalid.treeTokenAccount.1).1
  obtain ⟨hcfgAddr, _⟩ := wf.config _ _ hvalid.globalConfig.1
  have htreeAt : s.treeAccount d.treeAddress = tree := by
    simp only [PrivacyCash.Model.State.treeAccount, ← htreeAddr, hvalid.treeAccount.1.2]
  have hcfgAt : s.configAccount d.configAddress = config := by
    simp only [PrivacyCash.Model.State.configAccount, ← hcfgAddr, hvalid.globalConfig.1.2]
  have hT : W.state.tree = toTree tree := by
    show toTree (s.treeAccount d.treeAddress) = _; rw [htreeAt]
  have hC : W.state.config = toConfig config tree := by
    show toConfig (s.configAccount d.configAddress) (s.treeAccount d.treeAddress) = _; rw [htreeAt, hcfgAt]
  have hP : W.state.pool = H.state.pool := by
    show toPubkey d.poolAddress = toPubkey a.treeTokenAccount; rw [hpoolAddr]
  have hstate : H.state = { W.state with tree := toTree tree, config := toConfig config tree } := by
    show Spec.State.mk (toTree tree) (nullifierAccountsOf d s) (toPubkey a.treeTokenAccount)
        (nullifierAddrOf d) (toConfig config tree) (toPubkey a.treeAccount) (toPubkey a.globalConfig)
      = Spec.State.mk (toTree tree) (nullifierAccountsOf d s) (toPubkey d.poolAddress)
        (nullifierAddrOf d) (toConfig config tree) (toPubkey d.treeAddress) (toPubkey d.configAddress)
    rw [hpoolAddr, htreeAddr, hcfgAddr]
  -- the addresses of the new nullifier accounts
  obtain ⟨ha0, ha1⟩ := newNullifierAccount_toWorld d rent s tx.signers a proof ext fee out1 out2
  have hnf0 : a.nullifier0 = d.pda (nullifier0Seeds proof.input_nullifiers.val[0]!) := hvalid.nullifier0.1
  have hnf1 : a.nullifier1 = d.pda (nullifier1Seeds proof.input_nullifiers.val[1]!) := hvalid.nullifier1.1
  rw [← hnf0] at ha0; rw [← hnf1] at ha1
  obtain ⟨hsP, hs0, hs1⟩ := pre.signerNotPoolNotNullifiers
  obtain ⟨h01, -, -⟩ := pre.nullifierAccountsNew
  have hs0' : a.signer ≠ a.nullifier0 := fun e => hs0 (by rw [ha0]; show toPubkey a.signer = _; rw [e])
  have hs1' : a.signer ≠ a.nullifier1 := fun e => hs1 (by rw [ha1]; show toPubkey a.signer = _; rw [e])
  have h01' : a.nullifier0 ≠ a.nullifier1 := fun e => h01 (by rw [ha0, ha1, e])
  -- the handler's balances are the spec's after the rent step
  have hR := rentEffects_of_inits (signers := tx.signers) (ext := ext) (fee := fee) (out1 := out1)
    (out2 := out2) hnf0 hnf1 hs0' hs1' h01' hnr reached.inits
  have hHb : H.balances = (Spec.nullifierRentEffects inputs W).balances := by
    rw [hR]; rfl
  have hHr : H.nullifierRent = 0 := rfl
  have hsolv := pre.signerSolvency
  unfold Spec.signerSolvent at hsolv
  have hSolv : W.nullifierTopUp inputs 0 + W.nullifierTopUp inputs 1 ≤ W.balances inputs.s := by
    split_ifs at hsolv <;> omega
  have hrentB := Spec.nullifierRentEffects_balances inputs W hSolv hs0 hs1 h01
  have hdelta := balanceDelta_after_rent inputs W H hHb hP.symm hHr hSolv hs0 hs1 h01
  -- the pool keeps its balance
  have hpb : H.poolBalance = W.poolBalance := by
    unfold Spec.World.poolBalance
    rw [← hP, hHb]
    have := hrentB W.state.pool
    rw [if_neg (fun e => hsP (Or.inl e.symm)), if_neg (fun e => pre.nullifierAccountsNew.2.1 (Or.inl e.symm)),
      if_neg (fun e => pre.nullifierAccountsNew.2.2 (Or.inl e.symm))] at this
    omega
  -- the signer pays the top-ups first
  have hsig : (H.balances inputs.s : ℤ)
      = W.balances inputs.s - (W.nullifierTopUp inputs 0 + W.nullifierTopUp inputs 1) := by
    rw [hHb, hrentB, if_pos rfl, if_neg hs0, if_neg hs1]; ring
  have hfits := pre.balancesFit
  exact {
    knownRoot := by have h := pre.knownRoot; rw [hT] at h; exact h
    externalDataBinding := pre.externalDataBinding
    minimumFee := by have h := pre.minimumFee; rw [hC] at h; exact h
    pubAmtConsistency := pre.pubAmtConsistency
    validZKP := pre.validZKP
    newNullifiers := by
      have h := pre.newNullifiers; rw [show H.state = _ from hstate]; exact h
    distinctNullifiers := pre.distinctNullifiers
    nullifierAccountsNew := by
      have h := pre.nullifierAccountsNew; rw [show H.state = _ from hstate]; exact h
    depositLimit := by have h := pre.depositLimit; rw [hC] at h; exact h
    poolSolvency := by rw [hpb]; exact pre.poolSolvency
    signerSolvency := by
      unfold Spec.signerSolvent
      rw [nullifierTopUp_noRent inputs H hHr, nullifierTopUp_noRent inputs H hHr]
      have hs := hsig
      split_ifs at hsolv ⊢ <;> omega
    signerSignature := pre.signerSignature
    signerNotPoolNotNullifiers := by
      have h := pre.signerNotPoolNotNullifiers; rw [show H.state = _ from hstate]; exact h
    treeNotFull := by have h := pre.treeNotFull; rw [hT] at h; exact h
    amountRange := pre.amountRange
    solMint := pre.solMint
    encOutLength := pre.encOutLength
    poolNotRecipient := by rw [← hP]; exact pre.poolNotRecipient
    canonicalInputs := pre.canonicalInputs
    balancesFit := by
      refine ⟨fun x hpos => ?_, fun hext => ?_⟩
      · rw [hdelta x]
        by_cases hW : 0 < Spec.balanceDelta inputs W x
        · exact hfits.1 x hW
        · have : (W.balances x : ℤ) < 2 ^ 64 := by
            exact_mod_cast lamportsOf_lt s (fromPubkey x)
          omega
      · rw [hpb]; exact hfits.2 hext }

end

/-! ## Anchor's `init`s succeed -/

/-- A system transfer succeeds from a funded system account, when the destination's new balance
    fits. -/
theorem systemTransfer_some {s : State} {src dst : Pubkey} {x : U64} (hne : src ≠ dst)
    (ho : (s src).owner = systemProgram) (hd : (s src).data.isEmpty)
    (hle : x.val ≤ (s src).lamports.val) (hfit : (s dst).lamports.val + x.val ≤ U64.max) :
    ∃ s', s.systemTransfer src dst x = some s' := by
  have hb₁ : (setBalance s.balances src ⟨(s.balances src).bv - x.bv⟩ dst) = s.balances dst := by
    simp [setBalance, Ne.symm hne]
  unfold State.systemTransfer systemTransferBalances
  have hc : (s src).owner = systemProgram ∧ (s src).data.isEmpty = true ∧ x.val ≤ (s.balances src).val :=
    ⟨ho, hd, hle⟩
  rw [if_pos hc]
  have hf : (setBalance s.balances src ⟨(s.balances src).bv - x.bv⟩ dst).val + x.val ≤ U64.max := by
    rw [hb₁]; exact hfit
  simp only [hf, if_true, Option.map_some]
  exact ⟨_, rfl⟩

/-- Anchor's `init` succeeds when the payer is a different, plain system account holding what
    the address is missing to hold the rent. -/
theorem initAccount_some {pid : Pubkey} {s : State} {mb : Nat → U64} {payer key : Pubkey}
    {space : Nat} {data : AccountData} (hne : payer ≠ key)
    (ho : (s payer).owner = systemProgram) (hd : (s payer).data.isEmpty)
    (hle : (mb space).val - (s key).lamports.val ≤ (s payer).lamports.val) (hpos : 0 < (mb space).val) :
    ∃ s', s.initAccount pid mb payer key space data = some s' := by
  have hmax : (mb space).val ≤ U64.max := by scalar_tac
  unfold State.initAccount
  by_cases hz : (s key).lamports.val = 0
  · obtain ⟨s', h⟩ := systemTransfer_some (x := mb space) hne ho hd (by omega) (by omega)
    simp only [hz, if_true, h, Option.map_some]
    exact ⟨_, rfl⟩
  · simp only [hz, if_false, hne]
    by_cases ht : (max (mb space).val 1) - (s key).lamports.val = 0
    · simp only [ht, if_true, Option.map_some]
      exact ⟨_, rfl⟩
    · simp only [ht, if_false]
      have hm : max (mb space).val 1 = (mb space).val := by omega
      have hlt : (max (mb space).val 1) - (s key).lamports.val < 2 ^ 64 := by
        have := u64_lt (mb space); omega
      have hval : ((⟨BitVec.ofNat 64 ((max (mb space).val 1) - (s key).lamports.val)⟩ : U64)).val
          = (max (mb space).val 1) - (s key).lamports.val := by
        show (BitVec.ofNat 64 _).toNat = _
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hlt
      obtain ⟨s', h⟩ := systemTransfer_some
        (x := ⟨BitVec.ofNat 64 ((max (mb space).val 1) - (s key).lamports.val)⟩) hne ho hd
        (by rw [hval]; omega) (by rw [hval]; omega)
      rw [h]
      exact ⟨_, rfl⟩

/-- The two `init`s of a `transact` succeed when the signer is a plain system account holding
    what the two nullifier addresses are missing to hold the rent. -/
theorem inits_some {pid : Pubkey} {s : State} {mb : Nat → U64} {signer n0 n1 : Pubkey}
    {space : Nat} {data : AccountData} (hpos : 0 < (mb space).val)
    (h0 : signer ≠ n0) (h1 : signer ≠ n1) (h01 : n0 ≠ n1)
    (ho : (s signer).owner = systemProgram) (hd : (s signer).data.isEmpty)
    (hle : ((mb space).val - (s n0).lamports.val) + ((mb space).val - (s n1).lamports.val)
      ≤ (s signer).lamports.val) :
    ∃ s₁, (s.initAccount pid mb signer n0 space data).bind
      (·.initAccount pid mb signer n1 space data) = some s₁ := by
  obtain ⟨sA, hA⟩ := initAccount_some (pid := pid) (space := space) (data := data) h0 ho hd
    (by omega) hpos
  obtain ⟨top0, _, _, _, hex0, hlamA, _, _, hother⟩ := initAccount_spec h0 hA
  have hsA : (sA signer).lamports.val = (s signer).lamports.val - top0 := by
    have := congrFun hlamA signer
    simp only [moveN, Function.update_of_ne h0, Function.update_self] at this; exact this
  have hzA : (sA n1).lamports.val = (s n1).lamports.val := by
    have := congrFun hlamA n1
    rw [moveN_other _ _ (Ne.symm h1) (Ne.symm h01)] at this; exact this
  have ht0 := hex0 hpos
  obtain ⟨s₁, h₁⟩ := initAccount_some (s := sA) (pid := pid) (mb := mb) (key := n1) (space := space)
    (data := data) h1 (by rw [(hother _ h0).1]; exact ho) (by rw [(hother _ h0).2]; exact hd)
    (by rw [hsA, hzA]; omega) hpos
  exact ⟨s₁, by simp [hA, h₁]⟩

/-! ## The runtime's lamport check passes -/

/-- Over a set of accounts containing every party, the spec's balance changes sum to zero, when
    no rent is charged. -/
theorem sum_balanceDelta_zero (inputs : Spec.TxInputs) (W : Spec.World) (a : TransactAccounts)
    (F : Finset Pubkey) (hW : W.nullifierRent = 0) (hp : W.state.pool = toPubkey a.treeTokenAccount)
    (hA : inputs.A = toPubkey a.recipient) (ht : inputs.t = toPubkey a.feeRecipientAccount)
    (hs : inputs.s = toPubkey a.signer)
    (mA : a.recipient ∈ F) (mt : a.feeRecipientAccount ∈ F) (ms : a.signer ∈ F)
    (mp : a.treeTokenAccount ∈ F) :
    ∑ k ∈ F, Spec.balanceDelta inputs W (toPubkey k) = 0 := by
  have hinj : ∀ {x y : Pubkey}, toPubkey x = toPubkey y ↔ x = y :=
    fun {x y} => ⟨fun h => toPubkey_inj h, fun h => by rw [h]⟩
  simp only [balanceDelta_noRent inputs W hW, hp]
  rw [hA, ht, hs]
  simp only [hinj]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [ite_and, Finset.sum_ite_eq', mA, mt, ms, mp, if_true]
  by_cases h1 : inputs.extAmt < 0
  · have h2 : ¬ inputs.extAmt > 0 := by omega
    simp only [h1, h2, if_true, if_false]
    omega
  · by_cases h2 : inputs.extAmt > 0
    · simp only [h1, h2, if_true, if_false]; omega
    · simp only [h1, h2, if_false]; omega


/-! ## `execTransact` accepts -/

theorem checkBalanced_ok {s s' : State} {keys : List Pubkey}
    (h : s'.totalLamports keys = s.totalLamports keys) : checkBalanced s s' keys = .ok s' := by
  unfold checkBalanced
  exact if_pos h

seal checkBalanced in
/-- `execTransact` is its parts: Anchor's checks, the `init`s, the handler, the lamport check. -/
theorem execTransact_of_parts
    {d : Deployment} {rent : Nat → U64} {s s₁ : State} {tx : TxEnv}
    {a : TransactAccounts} {proof : zkcash_core.transact.Proof} {ext : I64} {fee : U64}
    {out1 out2 : Slice U8} {tree tree' : zkcash_core.merkle_tree.MerkleTreeAccount}
    {tt : zkcash_core.admin.TreeTokenAccount} {config : zkcash_core.admin.GlobalConfig}
    {ap : zkcash_core.transact.Appended} {env' : SolEnv}
    (hT : (s a.treeAccount).data = .treeAccount tree)
    (hP : (s a.treeTokenAccount).data = .treeToken tt)
    (hC : (s a.globalConfig).data = .globalConfig config)
    (hvalid : TransactAccountsValid d.toAddresses s tx.toTxContext a proof.input_nullifiers.val[0]!
      proof.input_nullifiers.val[1]! tree tt config)
    (hrent : tx.minimumBalance = some rent)
    (hinits : (s.initAccount d.programId rent a.signer a.nullifier0 nullifierAccountSpace (.nullifier 0#u8)).bind
      (·.initAccount d.programId rent a.signer a.nullifier1 nullifierAccountSpace (.nullifier 0#u8)) = some s₁)
    (hR : ofResult (zkcash_core.transact.transact d.crypto.hasher arkFr d.crypto.sha256
      d.crypto.proofVerifier solRuntime (handlerEnv a s₁ (rent treeTokenAccountSpace)) tree config proof
      ext fee a.recipient a.feeRecipientAccount out1 out2) = .ok (.Ok ap, env', tree'))
    (hcons : (((s₁.withBalances env'.balances).set a.treeAccount
        { (s₁.withBalances env'.balances) a.treeAccount with data := .treeAccount tree' })).totalLamports
        (txKeys a) = s.totalLamports (txKeys a)) :
    execTransact d s tx a proof ext fee out1 out2 = .ok
      ((s₁.withBalances env'.balances).set a.treeAccount
        { (s₁.withBalances env'.balances) a.treeAccount with data := .treeAccount tree' },
       [⟨ap.first_index, proof.output_commitments.val[0]!, out1.val⟩,
        ⟨ap.second_index, proof.output_commitments.val[1]!, out2.val⟩]) := by
  unfold execTransact
  simp only [hT, hP, hC]
  rw [if_neg (not_not.mpr hvalid)]
  simp only [hrent, hinits]
  have hR' : ofResult (zkcash_core.transact.transact d.crypto.hasher arkFr d.crypto.sha256
      d.crypto.proofVerifier solRuntime
      { accounts := s₁, balances := s₁.balances, signer := a.signer, treeToken := a.treeTokenAccount,
        recipient := a.recipient, feeRecipient := a.feeRecipientAccount,
        rentExemptMinimum := some (rent treeTokenAccountSpace) }
      tree config proof ext fee a.recipient a.feeRecipientAccount out1 out2)
      = .ok (.Ok ap, env', tree') := hR
  simp only [hR']
  have hB : checkBalanced s ((s₁.withBalances env'.balances).set a.treeAccount
      { (s₁.withBalances env'.balances) a.treeAccount with data := .treeAccount tree' })
      [a.treeAccount, a.nullifier0, a.nullifier1, a.nullifier2, a.nullifier3, a.treeTokenAccount,
       a.globalConfig, a.recipient, a.feeRecipientAccount, a.signer, a.systemProgram]
      = .ok ((s₁.withBalances env'.balances).set a.treeAccount
      { (s₁.withBalances env'.balances) a.treeAccount with data := .treeAccount tree' }) :=
    checkBalanced_ok hcons
  show (checkBalanced s ((s₁.withBalances env'.balances).set a.treeAccount
      { (s₁.withBalances env'.balances) a.treeAccount with data := .treeAccount tree' })
      [a.treeAccount, a.nullifier0, a.nullifier1, a.nullifier2, a.nullifier3, a.treeTokenAccount,
       a.globalConfig, a.recipient, a.feeRecipientAccount, a.signer, a.systemProgram]
      >>= fun s' => Except.ok (s',
        ([⟨ap.first_index, proof.output_commitments.val[0]!, out1.val⟩,
          ⟨ap.second_index, proof.output_commitments.val[1]!, out2.val⟩] : List CommitmentData))) = _
  rw [hB]
  rfl


section
variable {G1 G2 GT : Type} [AddCommGroup G1] [Module Spec.F G1] [Inhabited G2]
  [CommGroup GT] [Spec.PoseidonHashes] [Spec.Sha]

/-- **`execTransact` accepts.** If the accounts pass Anchor's checks and the spec's preconditions
    hold in the code's world, Anchor's `init`s, the handler and the runtime's lamport check all
    succeed. L1 and A0 are excluded by name. -/
theorem execTransact_complete
    {d : Deployment} {rent : Nat → U64} {s : State} {tx : TxEnv}
    {a : TransactAccounts} {proof : zkcash_core.transact.Proof} {ext : I64} {fee : U64}
    {out1 out2 : Slice U8} {tree : zkcash_core.merkle_tree.MerkleTreeAccount}
    {tt : zkcash_core.admin.TreeTokenAccount} {config : zkcash_core.admin.GlobalConfig}
    (C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT) (laws : PairingLaws C.e)
    (hashes : HashesAgree d) (crypto : CryptoSucceeds d.crypto C)
    (h64 : Usize.max = 2^64 - 1) (wf : WellFormed d s)
    (hnr : 0 < (rent nullifierAccountSpace).val)
    (hvalid : TransactAccountsValid d.toAddresses s tx.toTxContext a proof.input_nullifiers.val[0]!
      proof.input_nullifiers.val[1]! tree tt config)
    (hrent : tx.minimumBalance = some rent)
    (hsigSys : (s a.signer).owner = systemProgram ∧ (s a.signer).data.isEmpty)
    (notL1 : ext.val ≠ 0)
    (notA0 : proof.proof_a.val ≠ List.replicate 64 0#u8) :
    withSyscallSpec C in
    let inputs := toInputs ⟨⟨tx.signers⟩, a, ⟨proof, ext, fee, out1, out2⟩⟩
    Spec.transactPreconditions inputs (toWorld d rent s) →
    ∃ s' evs, execTransact d s tx a proof ext fee out1 out2 = .ok (s', evs) := by
  withSyscallSpec C
  intro inputs pre
  -- the signer and the two nullifier addresses, as the spec sees them
  obtain ⟨ha0, ha1⟩ := newNullifierAccount_toWorld d rent s tx.signers a proof ext fee out1 out2
  rw [← hvalid.nullifier0.1] at ha0; rw [← hvalid.nullifier1.1] at ha1
  obtain ⟨-, hs0, hs1⟩ := pre.signerNotPoolNotNullifiers
  obtain ⟨h01, -, -⟩ := pre.nullifierAccountsNew
  have hs0' : a.signer ≠ a.nullifier0 := fun e => hs0 (by rw [ha0]; show toPubkey a.signer = _; rw [e])
  have hs1' : a.signer ≠ a.nullifier1 := fun e => hs1 (by rw [ha1]; show toPubkey a.signer = _; rw [e])
  have h01' : a.nullifier0 ≠ a.nullifier1 := fun e => h01 (by rw [ha0, ha1, e])
  -- the signer pays what the two addresses are missing
  have hfunds : ((rent nullifierAccountSpace).val - (s a.nullifier0).lamports.val)
      + ((rent nullifierAccountSpace).val - (s a.nullifier1).lamports.val) ≤ (s a.signer).lamports.val := by
    have hT0 : (toWorld d rent s).nullifierTopUp inputs 0
        = (rent nullifierAccountSpace).val - (s a.nullifier0).lamports.val := by
      unfold Spec.World.nullifierTopUp; rw [ha0]
      show _ - (s (fromPubkey (toPubkey a.nullifier0))).lamports.val = _; rw [fromPubkey_toPubkey]; rfl
    have hT1 : (toWorld d rent s).nullifierTopUp inputs 1
        = (rent nullifierAccountSpace).val - (s a.nullifier1).lamports.val := by
      unfold Spec.World.nullifierTopUp; rw [ha1]
      show _ - (s (fromPubkey (toPubkey a.nullifier1))).lamports.val = _; rw [fromPubkey_toPubkey]; rfl
    have hsb : (toWorld d rent s).balances inputs.s = (s a.signer).lamports.val := by
      show (s (fromPubkey (toPubkey a.signer))).lamports.val = _; rw [fromPubkey_toPubkey]
    have h := pre.signerSolvency
    unfold Spec.signerSolvent at h
    rw [hT0, hT1, hsb] at h
    split_ifs at h <;> omega
  obtain ⟨s₁, hinits⟩ := inits_some (pid := d.programId) (space := nullifierAccountSpace)
    (data := .nullifier 0#u8) hnr hs0' hs1' h01' hsigSys.1 hsigSys.2 hfunds
  have reached : ReachedHandler d rent s tx a proof tree tt config s₁ := ⟨hvalid, hrent, hinits⟩
  have allows := preconditions_at_handler wf reached hnr pre
  -- the handler accepts
  obtain ⟨ho, hd, _, _, _⟩ := after_inits hs0' hs1' hinits
  obtain ⟨_, hshape, _⟩ := wf.tree _ _ hvalid.treeAccount.1
  obtain ⟨_, hdr, hwr, hmr, _⟩ := wf.config _ _ hvalid.globalConfig.1
  obtain ⟨ap, env', tree', hrun, hbal, -⟩ :=
    handler_complete_exact' d C laws hashes crypto.poseidonSucceeds crypto.sha256Succeeds
      crypto.syscallsSucceed crypto.keyDecodes a s₁ (rent treeTokenAccountSpace) tree config
      (nullifierAccountsOf d s)
      (nullifierAddrOf d) proof ext fee out1 out2 hshape
      (wf.storedRoots _ _ hvalid.treeAccount.1) (wf.storedSubtrees _ _ hvalid.treeAccount.1) hdr hwr hmr
      ⟨ho.trans hsigSys.1, by rw [hd]; exact hsigSys.2⟩ h64 notL1 notA0 allows
  -- the runtime's lamport check
  let s₂ := s₁.withBalances env'.balances
  let s₃ := s₂.set a.treeAccount { s₂ a.treeAccount with data := .treeAccount tree' }
  set H := handlerWorld a s₁ (rent treeTokenAccountSpace) tree config (nullifierAccountsOf d s)
    (nullifierAddrOf d) with hH
  have hcons : s₃.totalLamports (txKeys a) = s.totalLamports (txKeys a) := by
    have e₃ : (fun k => (s₃ k).lamports.val) = fun k => (env'.balances k).val := by
      funext k
      by_cases hk : k = a.treeAccount
      · subst hk; simp [s₃, s₂, State.withBalances]
      · simp [s₃, s₂, hk, State.withBalances]
    have hTLenv : TL (txKeys a) (fun k => (env'.balances k).val)
        = TL (txKeys a) (fun k => (s₁ k).lamports.val) := by
      unfold TL
      have hk : ∀ k, ((env'.balances k).val : ℤ) = (s₁ k).lamports.val
          + Spec.balanceDelta inputs H (toPubkey k) := by
        intro k
        rw [hbal k]
        have := Spec.transactEffects_balances inputs H
          allows.signerSolvency allows.poolSolvency allows.poolNotRecipient
          allows.signerNotPoolNotNullifiers allows.nullifierAccountsNew (toPubkey k)
        rw [this]
        show (((s₁ (fromPubkey (toPubkey k))).lamports.val : ℕ) : ℤ) + _ = _
        rw [fromPubkey_toPubkey]
      simp only [hk]
      rw [Finset.sum_add_distrib,
        sum_balanceDelta_zero inputs H a _ rfl rfl rfl rfl rfl
          (List.mem_toFinset.mpr (by simp [txKeys])) (List.mem_toFinset.mpr (by simp [txKeys]))
          (List.mem_toFinset.mpr (by simp [txKeys])) (List.mem_toFinset.mpr (by simp [txKeys])), add_zero]
    have hTLinit : TL (txKeys a) (fun k => (s₁ k).lamports.val)
        = TL (txKeys a) (fun k => (s k).lamports.val) := by
      obtain ⟨sA, hA1, hA2⟩ := Option.bind_eq_some_iff.mp hinits
      obtain ⟨t0, hle0, _, _, _, hlam0, _⟩ := initAccount_spec hs0' hA1
      obtain ⟨t1, hle1, _, _, _, hlam1, _⟩ := initAccount_spec hs1' hA2
      rw [hlam1, TL_moveN (by simp [txKeys]) (by simp [txKeys]) _ hle1, hlam0,
        TL_moveN (by simp [txKeys]) (by simp [txKeys]) _ hle0]
    have : (s₃.totalLamports (txKeys a) : ℤ) = s.totalLamports (txKeys a) := by
      rw [totalLamports_eq, totalLamports_eq, e₃, hTLenv, hTLinit]
    exact_mod_cast this
  exact ⟨s₃, _, execTransact_of_parts hvalid.treeAccount.1.2 hvalid.treeTokenAccount.1.2
    hvalid.globalConfig.1.2 hvalid hrent hinits (by rw [hrun]; rfl) hcons⟩

/-! ## Anchor's account checks pass -/

omit [Spec.PoseidonHashes] [Spec.Sha] in
/-- Two derived addresses whose seeds have different lengths differ, when their derivation is
    collision-free. -/
theorem pda_ne_of_length {A : Addresses} {S : Set (List U8)} (hcf : DistinctAddresses A S)
    {x y : List U8} (hx : A.pdaInput x ∈ S) (hy : A.pdaInput y ∈ S) (hlen : x.length ≠ y.length) :
    A.pda x ≠ A.pda y :=
  ne_of_distinct hcf hx hy (fun h => hlen (by
    have := congrArg List.length h; simpa [Addresses.pdaInput] using this))

omit [Spec.PoseidonHashes] [Spec.Sha] in
/-- A derived address that holds none of the program's accounts is an untouched system
    account, so Anchor's `init` and `SystemAccount` constraints pass there. -/
theorem pda_untouched {d : Deployment} {s : State} (wf : WellFormed d s) (pdas : PdasOnlyByProgram d s)
    (seeds : List U8) (hn : ¬ d.IsNullifierAccount s (d.pda seeds))
    (ht : d.pda seeds ≠ d.treeAddress) (hp : d.pda seeds ≠ d.poolAddress) (hc : d.pda seeds ≠ d.configAddress) :
    Initializable s (d.pda seeds) := by
  rcases pdas seeds with ⟨ho, hd⟩ | h
  · cases hdata : (s (d.pda seeds)).data with
    | treeAccount t => exact absurd (wf.tree _ t ⟨ho, hdata⟩).1 ht
    | treeToken p => exact absurd (wf.pool _ p ⟨ho, hdata⟩).1 hp
    | globalConfig c => exact absurd (wf.config _ c ⟨ho, hdata⟩).1 hc
    | nullifier b => exact absurd ⟨ho, b, hdata⟩ hn
    | empty => rw [hdata] at hd; simp [AccountData.isProgramData] at hd
    | foreign => rw [hdata] at hd; simp [AccountData.isProgramData] at hd
  · exact h

omit [Spec.PoseidonHashes] [Spec.Sha] in
/-- **Anchor's account checks pass**, for the tree, pool and config the program holds: their
    stored bumps are the canonical ones (`WellFormed`), and the spec's `nullifiersFresh` leaves the
    four nullifier addresses untouched system accounts. -/
theorem accounts_valid
    {d : Deployment} {rent : Nat → U64} {s : State} {tx : TxEnv}
    {a : TransactAccounts} {proof : zkcash_core.transact.Proof} {ext : I64} {fee : U64}
    {out1 out2 : Slice U8} {tree : zkcash_core.merkle_tree.MerkleTreeAccount}
    {tt : zkcash_core.admin.TreeTokenAccount} {config : zkcash_core.admin.GlobalConfig}
    (wf : WellFormed d s) (pdas : PdasOnlyByProgram d s)
    (noCollision : TransactAddressesDistinct d proof) (accounts : AccountsListed d a proof)
    (hT : HoldsTree d.programId s d.treeAddress tree) (hP : HoldsTreeToken d.programId s d.poolAddress tt)
    (hC : HoldsGlobalConfig d.programId s d.configAddress config)
    (hsigned : a.signer ∈ tx.signers)
    (fresh : Spec.nullifiersFresh (toWorld d rent s).state (toInputs ⟨⟨tx.signers⟩, a, ⟨proof, ext, fee, out1, out2⟩⟩)) :
    TransactAccountsValid d.toAddresses s tx.toTxContext a proof.input_nullifiers.val[0]!
      proof.input_nullifiers.val[1]! tree tt config := by
  set inputs := toInputs ⟨⟨tx.signers⟩, a, ⟨proof, ext, fee, out1, out2⟩⟩ with hinputs
  -- the spec's "fresh": none of the four addresses holds a nullifier account
  have hby0 : inputs.nullifierBytes 0 = toBytes proof.input_nullifiers.val[0]!.val := by
    simp [inputs, toInputs, Spec.TxInputs.nullifierBytes, publicInputs]
  have hby1 : inputs.nullifierBytes 1 = toBytes proof.input_nullifiers.val[1]!.val := by
    simp [inputs, toInputs, Spec.TxInputs.nullifierBytes, publicInputs]
  obtain ⟨hf0, hf1⟩ := fresh
  have notNull : ∀ (n : Pubkey), ¬ (toWorld d rent s).state.spent (toBytes n.val) →
      ¬ d.IsNullifierAccount s (d.pda (nullifier0Seeds n)) ∧
      ¬ d.IsNullifierAccount s (d.pda (nullifier1Seeds n)) := by
    intro n hn
    obtain ⟨e0, e1⟩ := nullifierAddrOf_bytes d n
    refine ⟨fun h => hn (Or.inl ?_), fun h => hn (Or.inr ?_)⟩
    · show nullifierAddrOf d 0 _ ∈ nullifierAccountsOf d s
      rw [e0, mem_nullifierAccountsOf, fromPubkey_toPubkey]; exact h
    · show nullifierAddrOf d 1 _ ∈ nullifierAccountsOf d s
      rw [e1, mem_nullifierAccountsOf, fromPubkey_toPubkey]; exact h
  rw [hby0] at hf0; rw [hby1] at hf1
  obtain ⟨hn00, hn10⟩ := notNull _ hf0
  obtain ⟨hn01, hn11⟩ := notNull _ hf1
  -- so they are untouched system accounts: they are not the tree, the pool or the config either
  obtain ⟨hlT, -, hlP, hlC, -, -⟩ := seed_lengths proof.input_nullifiers.val[0]! proof.input_nullifiers.val[0]!
  have len0 : ∀ n : Pubkey, (nullifier0Seeds n).length = 42 := fun n => (seed_lengths n n).2.2.2.2.1
  have len1 : ∀ n : Pubkey, (nullifier1Seeds n).length = 42 := fun n => (seed_lengths n n).2.2.2.2.2
  have free : ∀ seeds, d.pdaInput seeds ∈ transactSeeds d proof →
      seeds.length = 42 → ¬ d.IsNullifierAccount s (d.pda seeds) → Initializable s (d.pda seeds) := by
    intro seeds hmem hlen hn
    exact pda_untouched wf pdas seeds hn
      (pda_ne_of_length noCollision hmem (by simp [transactSeeds, fixedSeeds])
        (by rw [hlen, hlT]; decide))
      (pda_ne_of_length noCollision hmem (by simp [transactSeeds, fixedSeeds])
        (by rw [hlen, hlP]; decide))
      (pda_ne_of_length noCollision hmem (by simp [transactSeeds, fixedSeeds])
        (by rw [hlen, hlC]; decide))
  have i0 := free _ (by simp [transactSeeds]) (len0 _) hn00
  have i1 := free _ (by simp [transactSeeds]) (len1 _) hn11
  have i2 := free _ (by simp [transactSeeds]) (len0 _) hn01
  have i3 := free _ (by simp [transactSeeds]) (len1 _) hn10
  exact {
    treeAccount := by rw [accounts.tree]; exact ⟨hT, by rw [(wf.tree _ _ hT).2.2]; rfl⟩
    nullifier0 := by rw [accounts.nullifier0]; exact ⟨rfl, i0⟩
    nullifier1 := by rw [accounts.nullifier1]; exact ⟨rfl, i1⟩
    nullifier2 := by rw [accounts.nullifier2]; exact ⟨rfl, i2.1⟩
    nullifier3 := by rw [accounts.nullifier3]; exact ⟨rfl, i3.1⟩
    treeTokenAccount := by rw [accounts.pool]; exact ⟨hP, by rw [(wf.pool _ _ hP).2]; rfl⟩
    globalConfig := by rw [accounts.config]; exact ⟨hC, by rw [(wf.config _ _ hC).2.2.2.2]; rfl⟩
    signer := hsigned
    systemProgram := accounts.systemProg }

/-- **Completeness of `transact` at the step level**: in a reachable, initialized state, what the
    spec allows, `step` accepts. L1 and A0 are excluded by name. -/
theorem transact_complete_pf
    {d : Deployment} {rent : Nat → U64} {s : State} {tx : TxEnv}
    {a : TransactAccounts} {proof : zkcash_core.transact.Proof} {ext : I64} {fee : U64}
    {out1 out2 : Slice U8}
    (reachable : Reachable d s) (hpid : d.programId ≠ systemProgram)
    (C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT) (laws : PairingLaws C.e)
    (hashes : HashesAgree d) (crypto : CryptoSucceeds d.crypto C) (runtime : RuntimeFacts rent)
    (pdas : PdasOnlyByProgram d s) (noCollision : TransactAddressesDistinct d proof)
    (sameRent : SameRent rent tx.minimumBalance)
    (accounts : AccountsListed d a proof) (signerPlain : SignerIsPlain s a)
    (initialized : Initialized d s)
    (notL1 : ext.val ≠ 0) (notA0 : proof.proof_a.val ≠ List.replicate 64 0#u8) :
    withSyscallSpec C in
    Spec.transactPreconditions (toInputs ⟨⟨tx.signers⟩, a, ⟨proof, ext, fee, out1, out2⟩⟩) (toWorld d rent s) →
      Accepts d s tx (.transact a proof ext fee out1 out2) := by
  withSyscallSpec C
  intro pre
  obtain ⟨_, _, hgen, hrun⟩ := reachable
  have wf := wf_reachable hgen hrun hpid hashes
  obtain ⟨⟨tree, hT⟩, ⟨tt, hP⟩, ⟨config, hC⟩⟩ := initialized
  have hsigned : a.signer ∈ tx.signers := by
    obtain ⟨k, hk, he⟩ := List.mem_map.mp pre.signerSignature
    rwa [← toPubkey_inj he]
  exact execTransact_complete C laws hashes crypto runtime.usize64 wf (runtime.rentPositive _)
    (accounts_valid wf pdas noCollision accounts hT hP hC hsigned pre.newNullifiers) sameRent
    signerPlain notL1 notA0 pre

/-! ## The result: what the spec allows ends in the spec's world -/


omit [Spec.PoseidonHashes] [Spec.Sha] in
/-- The spec's rent, positive and equal to the sysvar's, makes the transaction's rent positive. -/
theorem rentPositive_of_sameRent {rent : Nat → U64} {tx : TxEnv} (runtime : RuntimeFacts rent)
    (sameRent : SameRent rent tx.minimumBalance) : tx.RentPositive := by
  intro mb h n
  have : rent = mb := Option.some.inj (sameRent.symm.trans h)
  subst this
  exact runtime.rentPositive n
omit [Spec.PoseidonHashes] [Spec.Sha] in
/-- A world that agrees with another on every field is that world. -/
theorem agrees_eq {i : Spec.TxInputs} {p q : Spec.World}
    (h : Spec.AgreesOnProgramEffects i p q) : q = p := by
  obtain ⟨⟨t, n, po, na, c, ta, ca⟩, b, r, nr⟩ := q
  obtain ⟨⟨t', n', po', na', c', ta', ca'⟩, b', r', nr'⟩ := p
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  simp only at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  rfl

omit [Spec.PoseidonHashes] [Spec.Sha] in
/-- The completeness conclusion "`step` returns `newState` and `toWorld newState = w`" (a `match`),
    taken apart: `step` succeeds, and the world of its new state is `w`. -/
theorem step_ok_of_match {d : Deployment} {rent : Nat → U64} {s : State} {tx : TxEnv}
    {ix : Instruction} {w : Spec.World}
    (h : match step d s tx ix with
      | .ok (newState, _logs) => toWorld d rent newState = w
      | .error _ => False) :
    ∃ s' em, step d s tx ix = .ok (s', em) ∧ toWorld d rent s' = w := by
  split at h
  · rename_i s' em hs
    exact ⟨s', em, hs, h⟩
  · exact h.elim

/-- **Completeness of `transact` with its result**: in a reachable, initialized state, what the
    spec allows, `step` accepts, and its new state maps to the spec's `transactEffects`. The
    signer facts and the distinct nullifiers soundness needs come from the spec's preconditions. -/
theorem transact_complete_square_pf
    {d : Deployment} {rent : Nat → U64} {s : State} {tx : TxEnv}
    {a : TransactAccounts} {proof : zkcash_core.transact.Proof} {ext : I64} {fee : U64}
    {out1 out2 : Slice U8}
    (reachable : Reachable d s) (hpid : d.programId ≠ systemProgram)
    (C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT) (laws : PairingLaws C.e)
    (hashes : HashesAgree d) (crypto : CryptoSucceeds d.crypto C) (runtime : RuntimeFacts rent)
    (pdas : PdasOnlyByProgram d s) (noCollision : TransactAddressesDistinct d proof)
    (sameRent : SameRent rent tx.minimumBalance)
    (accounts : AccountsListed d a proof) (signerPlain : SignerIsPlain s a)
    (initialized : Initialized d s)
    (notL1 : ext.val ≠ 0) (notA0 : proof.proof_a.val ≠ List.replicate 64 0#u8) :
    withSyscallSpec C in
    let inputs := toInputs ⟨⟨tx.signers⟩, a, ⟨proof, ext, fee, out1, out2⟩⟩
    Spec.transactPreconditions inputs (toWorld d rent s) →
      match step d s tx (.transact a proof ext fee out1 out2) with
      | .ok (newState, _logs) =>
          toWorld d rent newState = Spec.transactEffects inputs (toWorld d rent s)
      | .error _ => False := by
  withSyscallSpec C
  intro inputs pre
  obtain ⟨s', em, hstep⟩ := transact_complete_pf reachable hpid C laws hashes crypto runtime pdas
    noCollision sameRent accounts signerPlain initialized notL1 notA0 pre
  obtain ⟨_, _, hgen, hrun⟩ := reachable
  have wf := wf_reachable hgen hrun hpid hashes
  -- the signer is none of the program's accounts (`signerNotPoolNotNullifiers`)
  have hsNot := pre.signerNotPoolNotNullifiers
  have hsP : ¬ (toWorld d rent s).state.IsProgramAccount (toPubkey a.signer) := hsNot.1
  obtain ⟨ha0, ha1⟩ := newNullifierAccount_toWorld d rent s tx.signers a proof ext fee out1 out2
  have hsig : SignerNotProgram d s a := by
    refine ⟨fun e => hsP (Or.inl (by rw [e]; rfl)), fun e => hsP (Or.inr (Or.inr (Or.inl
      (by rw [e]; rfl)))), fun e => hsP (Or.inr (Or.inr (Or.inr (by rw [e]; rfl)))), ?_, ?_, ?_⟩
    · intro e; apply hsNot.2.1; rw [ha0, ← accounts.nullifier0]; exact congrArg toPubkey e
    · intro e; apply hsNot.2.2; rw [ha1, ← accounts.nullifier1]; exact congrArg toPubkey e
    · intro hn
      apply hsP
      refine Or.inr (Or.inl ?_)
      show toPubkey a.signer ∈ nullifierAccountsOf d s
      rw [mem_nullifierAccountsOf, fromPubkey_toPubkey]; exact hn
  -- the two input nullifiers differ (`distinctNullifiers`)
  have hcirc : CircuitFacts d {proof} := by
    refine ⟨fun p hp _ => ?_⟩
    rw [Set.mem_singleton_iff] at hp; subst hp
    intro e
    apply pre.distinctNullifiers
    exact congrArg toF e
  have htx := transact_refines_of hstep hashes wf hsig
    (rentPositive_of_sameRent runtime sameRent) (newDiffer_of_distinct noCollision) hcirc sameRent
    (fun _ => pre.validZKP) rfl
  rw [hstep]
  exact agrees_eq htx.2

/-! ## What the code never accepts (findings L1 and A0) -/

omit [Spec.PoseidonHashes] [Spec.Sha] in
/-- L1: an accepted `transact` has a non-zero external amount (`check_public_amount`). -/
theorem accepts_ext_ne_zero {d : Deployment} {s : State} {tx : TxEnv} {a : TransactAccounts}
    {proof : zkcash_core.transact.Proof} {ext : I64} {fee : U64} {out1 out2 : Slice U8}
    (h : Accepts d s tx (.transact a proof ext fee out1 out2)) : ext.val ≠ 0 := by
  obtain ⟨s', ev, hx⟩ := h
  obtain ⟨tree, tt, config, mb, s₁, env', tree', ap, -, -, -, hhandler, -⟩ :=
    execTransact_ok (show execTransact d s tx a proof ext fee out1 out2 = .ok (s', ev) from hx)
  have h2 := (handler_ok d.crypto d.crypto.sha256 _ tree config proof ext fee a.recipient a.feeRecipientAccount
    out1 out2 ap env' tree' hhandler).pubAmt
  rw [checkPublicAmount_eq] at h2
  exact (of_decide_eq_true (Result.ok_injective h2)).2.2

omit [Spec.PoseidonHashes] [Spec.Sha] in
/-- A0: an accepted `transact`'s `proof_a` is not the 64 zero bytes (`negate_g1`). -/
theorem accepts_proof_a_ne_zero {d : Deployment} {s : State} {tx : TxEnv} {a : TransactAccounts}
    {proof : zkcash_core.transact.Proof} {ext : I64} {fee : U64} {out1 out2 : Slice U8}
    (h : Accepts d s tx (.transact a proof ext fee out1 out2)) :
    proof.proof_a.val ≠ List.replicate 64 0#u8 := by
  intro hz
  obtain ⟨s', ev, hx⟩ := h
  obtain ⟨tree, tt, config, mb, s₁, env', tree', ap, -, -, -, hhandler, -⟩ :=
    execTransact_ok (show execTransact d s tx a proof ext fee out1 out2 = .ok (s', ev) from hx)
  have h2 := (handler_ok d.crypto d.crypto.sha256 _ tree config proof ext fee a.recipient a.feeRecipientAccount
    out1 out2 ap env' tree' hhandler).verify
  have h3 : d.crypto.proofVerifier.verify proof = ok false := verifyProof_zeroA proof _ hz
  rw [h3] at h2; simp at h2

end

end Connection
