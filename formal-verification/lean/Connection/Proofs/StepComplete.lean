import Connection.Proofs.HandlerComplete
import Connection.Proofs.Transact
import Spec.Statements
open Aeneas Aeneas.Std Result PrivacyCash.Model

/-! # Proofs: `transact` accepted through Anchor's `init`s and the runtime

NOT FOR REVIEW: used by G3a and G3b in `Connection/CodeModelStatements.lean`. If the accounts
pass Anchor's checks and the spec's preconditions hold, `execTransact` returns `ok`. -/

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
  obtain ⟨top0, _, _, _, hlamA, _, _, hotherA⟩ := initAccount_spec hs0 hA1
  obtain ⟨top1, _, _, _, hlam1, _, _, hother1⟩ := initAccount_spec hs1 hA2
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

/-- `OwnerAccounts s a`: account choices the honest owner makes: the signer is a plain system
    account, and neither payee is a nullifier account. -/
structure OwnerAccounts (s : State) (a : TransactAccounts) : Prop where
  signerSystem : (s a.signer).owner = systemProgram ∧ (s a.signer).data.isEmpty
  recipient : (∀ b, (s a.recipient).data ≠ .nullifier b) ∧ a.recipient ≠ a.nullifier0 ∧ a.recipient ≠ a.nullifier1
  feeRecipient : (∀ b, (s a.feeRecipientAccount).data ≠ .nullifier b) ∧
    a.feeRecipientAccount ≠ a.nullifier0 ∧ a.feeRecipientAccount ≠ a.nullifier1

section
variable [LeanSpec.PoseidonHashes] [LeanSpec.Sha] [LeanSpec.Groups] [AddCommGroup LeanSpec.G1]
  [Module LeanSpec.F LeanSpec.G1] [AddCommGroup LeanSpec.G2] [Module LeanSpec.F LeanSpec.G2]
  [CommGroup LeanSpec.GT] [LeanSpec.Pairing] [LeanSpec.Deployment]

/-- The spec's preconditions in the code's world give them in the world the handler sees. -/
theorem preconditions_at_handler
    {d : Deployment} {rent : Nat → U64} {spent : Finset LeanSpec.F} {s s₁ : State} {tx : TxEnv}
    {a : TransactAccounts} {proof : zkcash_core.transact.Proof} {ext : I64} {fee : U64}
    {out1 out2 : Slice U8} {tree : zkcash_core.merkle_tree.MerkleTreeAccount}
    {tt : zkcash_core.admin.TreeTokenAccount} {config : zkcash_core.admin.GlobalConfig}
    (wf : WellFormed d spent s)
    (reached : ReachedHandler d rent s tx a proof tree tt config s₁)
    (hs0 : a.signer ≠ a.nullifier0) (hs1 : a.signer ≠ a.nullifier1)
    (owner : OwnerAccounts s a)
    (hfit : ((s a.signer).lamports.val : ℤ) + LeanSpec.balanceDelta (toInputs tx.signers a proof ext fee out1 out2)
      (toPubkey (poolAddr d)) 0 (toPubkey a.signer) < 2^64)
    (pre : LeanSpec.transactPreconditions (toInputs tx.signers a proof ext fee out1 out2) (toWorld d rent spent s)) :
    LeanSpec.transactPreconditions (toInputs tx.signers a proof ext fee out1 out2)
      (handlerWorld a s₁ (rent treeTokenAccountSpace) tree config spent) := by
  have hvalid := reached.accounts
  obtain ⟨_, _, hge, hle, hoth⟩ := after_inits hs0 hs1 reached.inits
  obtain ⟨htreeAddr, _⟩ := wf.tree _ _ hvalid.treeAccount.1
  have hpoolAddr := wf.pool _ _ hvalid.treeTokenAccount.1
  obtain ⟨hcfgAddr, _⟩ := wf.config _ _ hvalid.globalConfig.1
  have htreeAt : treeAt s (treeAddr d) = tree := by
    simp only [treeAt, ← htreeAddr, hvalid.treeAccount.1.2]
  have hcfgAt : configAt s (configAddr d) = config := by
    simp only [configAt, ← hcfgAddr, hvalid.globalConfig.1.2]
  have hT : (toWorld d rent spent s).state.tree = toTree tree := by
    show toTree (treeAt s (treeAddr d)) = _; rw [htreeAt]
  have hC : (toWorld d rent spent s).state.config = toConfig config tree := by
    show toConfig (configAt s (configAddr d)) (treeAt s (treeAddr d)) = _; rw [htreeAt, hcfgAt]
  have hP : (toWorld d rent spent s).state.pool = toPubkey a.treeTokenAccount := by
    show toPubkey (poolAddr d) = _; rw [hpoolAddr]
  have hsep := pre.poolSeparate
  rw [hP] at hsep
  have hsigPool : a.signer ≠ a.treeTokenAccount := fun e => hsep.1 (by show toPubkey a.signer = _; rw [e])
  have hpool0 : a.treeTokenAccount ≠ a.nullifier0 := fun e => wf.programNotSystem (by
    rw [← hvalid.treeTokenAccount.1.1, e]; exact hvalid.nullifier0.2.1)
  have hpool1 : a.treeTokenAccount ≠ a.nullifier1 := fun e => wf.programNotSystem (by
    rw [← hvalid.treeTokenAccount.1.1, e]; exact hvalid.nullifier1.2.1)
  have hraw : ∀ c, c ≠ a.signer → c ≠ a.nullifier0 → c ≠ a.nullifier1 →
      (∀ b, (s c).data ≠ .nullifier b) → (s₁ c).lamports.val = publicBalance s c := by
    intro c h1 h2 h3 h4
    rw [hoth c h1 h2 h3, publicBalance_of h4]
  have hpoolData : ∀ b, (s a.treeTokenAccount).data ≠ .nullifier b := by
    intro b; rw [hvalid.treeTokenAccount.1.2]; simp
  have hpb : (handlerWorld a s₁ (rent treeTokenAccountSpace) tree config spent).poolBalance
      = (toWorld d rent spent s).poolBalance := by
    show (s₁ (fromPubkey (toPubkey a.treeTokenAccount))).lamports.val
      = publicBalance s (fromPubkey (toPubkey (poolAddr d)))
    rw [fromPubkey_toPubkey, fromPubkey_toPubkey, ← hpoolAddr]
    exact hraw _ (Ne.symm hsigPool) hpool0 hpool1 hpoolData
  have hsigData : ∀ b, (s a.signer).data ≠ .nullifier b := by
    intro b hb
    have := owner.signerSystem.2
    rw [hb] at this
    simp [AccountData.isEmpty] at this
  have hsigPub : publicBalance s a.signer = (s a.signer).lamports.val := publicBalance_of hsigData
  have hsigH : (handlerWorld a s₁ (rent treeTokenAccountSpace) tree config spent).balances (toPubkey a.signer)
      = (s₁ a.signer).lamports.val := by
    show (s₁ (fromPubkey (toPubkey a.signer))).lamports.val = _
    rw [fromPubkey_toPubkey]
  have hfits := pre.balancesFit
  exact {
    knownRoot := by have h := pre.knownRoot; rw [hT] at h; exact h
    externalDataBinding := pre.externalDataBinding
    minimumFee := by have h := pre.minimumFee; rw [hC] at h; exact h
    pubAmtConsistency := pre.pubAmtConsistency
    validZKP := pre.validZKP
    newNullifiers := pre.newNullifiers
    distinctNullifiers := pre.distinctNullifiers
    depositLimit := by have h := pre.depositLimit; rw [hC] at h; exact h
    poolSolvency := by rw [hpb]; exact pre.poolSolvency
    signerSolvency := by
      have h := pre.signerSolvency
      show (handlerWorld a s₁ (rent treeTokenAccountSpace) tree config spent).balances (toPubkey a.signer)
        ≥ 2 * 0 + (if (toInputs tx.signers a proof ext fee out1 out2).extAmt > 0
            then (toInputs tx.signers a proof ext fee out1 out2).extAmt.natAbs else 0)
      rw [hsigH]
      have h' : publicBalance s (fromPubkey (toPubkey a.signer))
          ≥ 2 * (rent nullifierAccountSpace).val + (if (toInputs tx.signers a proof ext fee out1 out2).extAmt > 0
            then (toInputs tx.signers a proof ext fee out1 out2).extAmt.natAbs else 0) := h
      rw [fromPubkey_toPubkey, hsigPub] at h'
      omega
    treeNotFull := by have h := pre.treeNotFull; rw [hT] at h; exact h
    amountRange := pre.amountRange
    encOutLength := pre.encOutLength
    poolSeparate := hsep
    canonicalInputs := pre.canonicalInputs
    signerSignature := pre.signerSignature
    balancesFit := by
      refine ⟨fun k hpos => ?_, fun hext => ?_⟩
      · set inputs := toInputs tx.signers a proof ext fee out1 out2 with hinputs
        have hkey : toPubkey (fromPubkey k) = k := toPubkey_fromPubkey k
        show ((s₁ (fromPubkey k)).lamports.val : ℤ)
          + LeanSpec.balanceDelta inputs (toPubkey a.treeTokenAccount) 0 k < 2^64
        have hpos' : 0 < LeanSpec.balanceDelta inputs (toPubkey a.treeTokenAccount) 0 k := hpos
        by_cases hks : k = toPubkey a.signer
        · subst hks
          rw [fromPubkey_toPubkey]
          rw [← hpoolAddr] at hfit
          have : ((s₁ a.signer).lamports.val : ℤ) ≤ (s a.signer).lamports.val := by exact_mod_cast hle
          linarith
        have hcs : fromPubkey k ≠ a.signer := fun e => hks (by rw [← hkey, e])
        have hdelta : LeanSpec.balanceDelta inputs (toWorld d rent spent s).state.pool
            (toWorld d rent spent s).nullifierRent k
            = LeanSpec.balanceDelta inputs (toPubkey a.treeTokenAccount) 0 k := by
          rw [hP]
          have hks' : k ≠ inputs.s := hks
          simp [LeanSpec.balanceDelta, hks']
        have hW := hfits.1 k (by rw [hdelta]; exact hpos')
        rw [hdelta] at hW
        have hWb : (toWorld d rent spent s).balances k = publicBalance s (fromPubkey k) := rfl
        rw [hWb] at hW
        suffices h : (s₁ (fromPubkey k)).lamports.val = publicBalance s (fromPubkey k) by
          rw [h]; exact hW
        by_cases hkA : k = toPubkey a.recipient
        · have e : fromPubkey k = a.recipient := by rw [hkA, fromPubkey_toPubkey]
          rw [e] at hcs ⊢
          exact hraw _ hcs owner.recipient.2.1 owner.recipient.2.2 owner.recipient.1
        by_cases hkt : k = toPubkey a.feeRecipientAccount
        · have e : fromPubkey k = a.feeRecipientAccount := by rw [hkt, fromPubkey_toPubkey]
          rw [e] at hcs ⊢
          exact hraw _ hcs owner.feeRecipient.2.1 owner.feeRecipient.2.2 owner.feeRecipient.1
        by_cases hkp : k = toPubkey a.treeTokenAccount
        · have e : fromPubkey k = a.treeTokenAccount := by rw [hkp, fromPubkey_toPubkey]
          rw [e] at hcs ⊢
          exact hraw _ hcs hpool0 hpool1 hpoolData
        exfalso
        have hA' : k ≠ inputs.A := hkA
        have ht' : k ≠ inputs.t := hkt
        have hs' : k ≠ inputs.s := hks
        simp [LeanSpec.balanceDelta, hA', ht', hs', hkp] at hpos'
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

/-- Anchor's `init` succeeds when the payer is a different, plain system account holding the
    rent. Whatever the address already holds, it needs at most the rent. -/
theorem initAccount_some {pid : Pubkey} {s : State} {mb : Nat → U64} {payer key : Pubkey}
    {space : Nat} {data : AccountData} (hne : payer ≠ key)
    (ho : (s payer).owner = systemProgram) (hd : (s payer).data.isEmpty)
    (hle : (mb space).val ≤ (s payer).lamports.val) (hpos : 0 < (mb space).val) :
    ∃ s', s.initAccount pid mb payer key space data = some s' := by
  have hmax : (mb space).val ≤ U64.max := by scalar_tac
  unfold State.initAccount
  by_cases hz : (s key).lamports.val = 0
  · obtain ⟨s', h⟩ := systemTransfer_some (x := mb space) hne ho hd hle (by omega)
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
    both rents. -/
theorem inits_some {pid : Pubkey} {s : State} {mb : Nat → U64} {signer n0 n1 : Pubkey}
    {space : Nat} {data : AccountData} (hpos : 0 < (mb space).val)
    (h0 : signer ≠ n0) (h1 : signer ≠ n1)
    (ho : (s signer).owner = systemProgram) (hd : (s signer).data.isEmpty)
    (hle : 2 * (mb space).val ≤ (s signer).lamports.val) :
    ∃ s₁, (s.initAccount pid mb signer n0 space data).bind
      (·.initAccount pid mb signer n1 space data) = some s₁ := by
  obtain ⟨sA, hA⟩ := initAccount_some (pid := pid) (space := space) (data := data) h0 ho hd
    (by omega) hpos
  obtain ⟨_, _, _, _, _, _, _, hother⟩ := initAccount_spec h0 hA
  have hge := initAccount_payer_ge h0 hA
  obtain ⟨s₁, h₁⟩ := initAccount_some (s := sA) (pid := pid) (mb := mb) (key := n1) (space := space)
    (data := data) h1 (by rw [(hother _ h0).1]; exact ho) (by rw [(hother _ h0).2]; exact hd)
    (by omega) hpos
  exact ⟨s₁, by simp [hA, h₁]⟩

/-! ## The runtime's lamport check passes -/

section
variable [LeanSpec.PoseidonHashes] [LeanSpec.Sha] [LeanSpec.Groups] [AddCommGroup LeanSpec.G1]
  [Module LeanSpec.F LeanSpec.G1] [AddCommGroup LeanSpec.G2] [Module LeanSpec.F LeanSpec.G2]
  [CommGroup LeanSpec.GT] [LeanSpec.Pairing] [LeanSpec.Deployment]

/-- Over a set of accounts containing every party, the spec's balance changes sum to zero, when
    no rent is charged. -/
theorem sum_balanceDelta_zero (inputs : LeanSpec.TxInputs) (a : TransactAccounts) (F : Finset Pubkey)
    (hA : inputs.A = toPubkey a.recipient) (ht : inputs.t = toPubkey a.feeRecipientAccount)
    (hs : inputs.s = toPubkey a.signer)
    (mA : a.recipient ∈ F) (mt : a.feeRecipientAccount ∈ F) (ms : a.signer ∈ F)
    (mp : a.treeTokenAccount ∈ F) :
    ∑ k ∈ F, LeanSpec.balanceDelta inputs (toPubkey a.treeTokenAccount) 0 (toPubkey k) = 0 := by
  have hinj : ∀ {x y : Pubkey}, toPubkey x = toPubkey y ↔ x = y :=
    fun {x y} => ⟨fun h => toPubkey_inj h, fun h => by rw [h]⟩
  unfold LeanSpec.balanceDelta
  rw [hA, ht, hs]
  simp only [hinj, Nat.cast_zero, mul_zero, ite_self, sub_zero]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [ite_and, Finset.sum_ite_eq', mA, mt, ms, mp, if_true]
  by_cases h1 : inputs.extAmt < 0
  · have h2 : ¬ inputs.extAmt > 0 := by omega
    simp only [h1, h2, if_true, if_false]
    omega
  · by_cases h2 : inputs.extAmt > 0
    · simp only [h1, h2, if_true, if_false]; omega
    · simp only [h1, h2, if_false]; omega

end

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
variable {G1 G2 GT : Type} [AddCommGroup G1] [Module LeanSpec.F G1] [AddCommGroup G2]
  [Module LeanSpec.F G2] [CommGroup GT] [LeanSpec.PoseidonHashes] [LeanSpec.Sha]

/-- **`execTransact` accepts.** If the accounts pass Anchor's checks and the spec's preconditions
    hold in the code's world, Anchor's `init`s, the handler and the runtime's lamport check all
    succeed. L1 and A0 are excluded by name. -/
theorem execTransact_complete
    {d : Deployment} {rent : Nat → U64} {spent : Finset LeanSpec.F} {s : State} {tx : TxEnv}
    {a : TransactAccounts} {proof : zkcash_core.transact.Proof} {ext : I64} {fee : U64}
    {out1 out2 : Slice U8} {tree : zkcash_core.merkle_tree.MerkleTreeAccount}
    {tt : zkcash_core.admin.TreeTokenAccount} {config : zkcash_core.admin.GlobalConfig}
    (C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT) (laws : PairingLaws C.e)
    (assume : CompletenessAssumptions d.crypto C)
    (wf : WellFormed d spent s)
    (hnr : 0 < (rent nullifierAccountSpace).val)
    (hvalid : TransactAccountsValid d.toAddresses s tx.toTxContext a proof.input_nullifiers.val[0]!
      proof.input_nullifiers.val[1]! tree tt config)
    (hrent : tx.minimumBalance = some rent)
    (owner : OwnerAccounts s a)
    (hs0 : a.signer ≠ a.nullifier0) (hs1 : a.signer ≠ a.nullifier1)
    (notL1 : ext.val ≠ 0)
    (notA0 : proof.proof_a.val ≠ List.replicate 64 0#u8) :
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    let inputs := toInputs tx.signers a proof ext fee out1 out2
    ((s a.signer).lamports.val : ℤ) + LeanSpec.balanceDelta inputs (toPubkey (poolAddr d)) 0
      (toPubkey a.signer) < 2^64 →
    LeanSpec.transactPreconditions inputs (toWorld d rent spent s) →
    ∃ s' evs, execTransact d s tx a proof ext fee out1 out2 = .ok (s', evs) := by
  letI : LeanSpec.Groups := syscallGroups C
  letI : LeanSpec.Pairing := syscallPairing C
  letI : LeanSpec.Deployment := ⟨programKey C⟩
  intro inputs hfit pre
  -- the signer pays both rents
  have hsigData : ∀ b, (s a.signer).data ≠ .nullifier b := by
    intro b hb
    have := owner.signerSystem.2
    rw [hb] at this
    simp [AccountData.isEmpty] at this
  have hfunds : 2 * (rent nullifierAccountSpace).val ≤ (s a.signer).lamports.val := by
    have h : publicBalance s (fromPubkey (toPubkey a.signer))
        ≥ 2 * (rent nullifierAccountSpace).val + (if inputs.extAmt > 0 then inputs.extAmt.natAbs else 0) :=
      pre.signerSolvency
    rw [fromPubkey_toPubkey, publicBalance_of hsigData] at h
    omega
  obtain ⟨s₁, hinits⟩ := inits_some (pid := d.programId) (space := nullifierAccountSpace)
    (data := .nullifier 0#u8) hnr hs0 hs1 owner.signerSystem.1 owner.signerSystem.2 hfunds
  have reached : ReachedHandler d rent s tx a proof tree tt config s₁ := ⟨hvalid, hrent, hinits⟩
  have allows := preconditions_at_handler wf reached hs0 hs1 owner hfit pre
  -- the handler accepts
  obtain ⟨ho, hd, _, _, _⟩ := after_inits hs0 hs1 hinits
  obtain ⟨_, hshape⟩ := wf.tree _ _ hvalid.treeAccount.1
  obtain ⟨_, hdr, hwr, hmr⟩ := wf.config _ _ hvalid.globalConfig.1
  obtain ⟨ap, env', tree', hrun, hbal, -⟩ :=
    handler_complete_exact' d.crypto C laws assume.hashesAgree assume.hashesSucceed assume.syscallsSucceed
      assume.keyDecodes a s₁ (rent treeTokenAccountSpace) tree config spent proof ext fee out1 out2 hshape
      (wf.storedRoots _ _ hvalid.treeAccount.1) (wf.storedSubtrees _ _ hvalid.treeAccount.1) hdr hwr hmr
      ⟨ho.trans owner.signerSystem.1, by rw [hd]; exact owner.signerSystem.2⟩ assume.usize64 notL1 notA0 allows
  -- the runtime's lamport check
  let s₂ := s₁.withBalances env'.balances
  let s₃ := s₂.set a.treeAccount { s₂ a.treeAccount with data := .treeAccount tree' }
  have hkeys : ∀ k ∈ [a.recipient, a.feeRecipientAccount, a.signer, a.treeTokenAccount], k ∈ txKeys a := by
    simp [txKeys]
  have hcons : s₃.totalLamports (txKeys a) = s.totalLamports (txKeys a) := by
    have e₃ : (fun k => (s₃ k).lamports.val) = fun k => (env'.balances k).val := by
      funext k
      by_cases hk : k = a.treeAccount
      · subst hk; simp [s₃, s₂, State.set, State.withBalances]
      · simp [s₃, s₂, State.set, hk, State.withBalances]
    have hTLenv : TL (txKeys a) (fun k => (env'.balances k).val)
        = TL (txKeys a) (fun k => (s₁ k).lamports.val) := by
      unfold TL
      have hk : ∀ k, ((env'.balances k).val : ℤ) = (s₁ k).lamports.val
          + LeanSpec.balanceDelta inputs (toPubkey a.treeTokenAccount) 0 (toPubkey k) := by
        intro k
        rw [hbal k]
        have := LeanSpec.transactEffects_balances inputs (handlerWorld a s₁ (rent treeTokenAccountSpace) tree config spent)
          allows.signerSolvency allows.poolSolvency allows.poolSeparate (toPubkey k)
        rw [this]
        show (((s₁ (fromPubkey (toPubkey k))).lamports.val : ℕ) : ℤ) + _ = _
        rw [fromPubkey_toPubkey]
        rfl
      simp only [hk]
      rw [Finset.sum_add_distrib,
        sum_balanceDelta_zero inputs a _ rfl rfl rfl
          (List.mem_toFinset.mpr (by simp [txKeys])) (List.mem_toFinset.mpr (by simp [txKeys]))
          (List.mem_toFinset.mpr (by simp [txKeys])) (List.mem_toFinset.mpr (by simp [txKeys])), add_zero]
    have hTLinit : TL (txKeys a) (fun k => (s₁ k).lamports.val)
        = TL (txKeys a) (fun k => (s k).lamports.val) := by
      obtain ⟨sA, hA1, hA2⟩ := Option.bind_eq_some_iff.mp hinits
      obtain ⟨t0, hle0, _, _, hlam0, _⟩ := initAccount_spec hs0 hA1
      obtain ⟨t1, hle1, _, _, hlam1, _⟩ := initAccount_spec hs1 hA2
      rw [hlam1, TL_moveN (by simp [txKeys]) (by simp [txKeys]) _ hle1, hlam0,
        TL_moveN (by simp [txKeys]) (by simp [txKeys]) _ hle0]
    have : (s₃.totalLamports (txKeys a) : ℤ) = s.totalLamports (txKeys a) := by
      rw [totalLamports_eq, totalLamports_eq, e₃, hTLenv, hTLinit]
    exact_mod_cast this
  exact ⟨s₃, _, execTransact_of_parts hvalid.treeAccount.1.2 hvalid.treeTokenAccount.1.2
    hvalid.globalConfig.1.2 hvalid hrent hinits (by rw [hrun]; rfl) hcons⟩

/-- The bundle gives Anchor's account checks, given the signer signed. -/
theorem ReachesProgram.valid
    {d : Deployment} {rent : Nat → U64} {s : State} {tx : TxEnv}
    {a : TransactAccounts} {proof : zkcash_core.transact.Proof} {ext : I64} {fee : U64}
    {out1 out2 : Slice U8} {tree : zkcash_core.merkle_tree.MerkleTreeAccount}
    {tt : zkcash_core.admin.TreeTokenAccount} {config : zkcash_core.admin.GlobalConfig}
    (reach : ReachesProgram d rent s tx a proof ext fee out1 out2 tree tt config)
    (hsigned : a.signer ∈ tx.signers) :
    TransactAccountsValid d.toAddresses s tx.toTxContext a proof.input_nullifiers.val[0]!
      proof.input_nullifiers.val[1]! tree tt config := by
  have hA := reach.accounts
  have hP := reach.program
  have hN := reach.nullifiers
  exact {
    treeAccount := by rw [hA.tree]; exact hP.tree
    nullifier0 := by rw [hA.nullifier0]; exact ⟨rfl, hN.new0⟩
    nullifier1 := by rw [hA.nullifier1]; exact ⟨rfl, hN.new1⟩
    nullifier2 := by rw [hA.nullifier2]; exact ⟨rfl, hN.other0⟩
    nullifier3 := by rw [hA.nullifier3]; exact ⟨rfl, hN.other1⟩
    treeTokenAccount := by rw [hA.pool]; exact hP.pool
    globalConfig := by rw [hA.config]; exact hP.config
    signer := hsigned
    systemProgram := hA.systemProg }

/-- A spec acceptance at the code's world is a code acceptance. L1 and A0 are excluded by name. -/
theorem step_accepts_of_spec
    {d : Deployment} {rent : Nat → U64} {spent : Finset LeanSpec.F} {s : State} {tx : TxEnv}
    {a : TransactAccounts} {proof : zkcash_core.transact.Proof} {ext : I64} {fee : U64}
    {out1 out2 : Slice U8} {tree : zkcash_core.merkle_tree.MerkleTreeAccount}
    {tt : zkcash_core.admin.TreeTokenAccount} {config : zkcash_core.admin.GlobalConfig}
    (C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT) (laws : PairingLaws C.e)
    (assume : CompletenessAssumptions d.crypto C) (wf : WellFormed d spent s)
    (reach : ReachesProgram d rent s tx a proof ext fee out1 out2 tree tt config)
    (notL1 : ext.val ≠ 0) (notA0 : proof.proof_a.val ≠ List.replicate 64 0#u8) :
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    ∀ w : LeanSpec.World, toWorld d rent spent s = w →
      LeanSpec.CanBeAccepted (toInputs tx.signers a proof ext fee out1 out2) w →
      ∃ s' evs, step d s tx (.transact a proof ext fee out1 out2) = .ok (s', evs) := by
  letI : LeanSpec.Groups := syscallGroups C
  letI : LeanSpec.Pairing := syscallPairing C
  letI : LeanSpec.Deployment := ⟨programKey C⟩
  intro w hw haccept
  have pre : LeanSpec.transactPreconditions (toInputs tx.signers a proof ext fee out1 out2)
      (toWorld d rent spent s) := by
    rw [hw]; exact haccept.1
  have hsigned : a.signer ∈ tx.signers := by
    obtain ⟨k, hk, he⟩ := List.mem_map.mp pre.signerSignature
    rwa [← toPubkey_inj he]
  have hA := reach.accounts
  have owner : OwnerAccounts s a := ⟨hA.signerPlain, hA.recipient, hA.feeRecipient⟩
  -- the signer is not a nullifier account: a PDA does not sign
  have hs0 : a.signer ≠ a.nullifier0 := fun e => reach.solana.pdasDoNotSign _ (by rw [← hA.nullifier0, ← e]; exact hsigned)
  have hs1 : a.signer ≠ a.nullifier1 := fun e => reach.solana.pdasDoNotSign _ (by rw [← hA.nullifier1, ← e]; exact hsigned)
  exact execTransact_complete C laws assume wf (reach.rentPositive rent reach.rentFixed _)
    (reach.valid hsigned) reach.rentFixed owner hs0 hs1 notL1 notA0 reach.signerCredit pre

end

end Connection
