import Connection.Assumptions
import Connection.Proofs.Handler
import Connection.Proofs.ExtData
open Aeneas Aeneas.Std Result PrivacyCash.Model

/-! # Proof of the connection theorem for `transact`

NOT FOR REVIEW: the statement is restated in `Connection/Statements.lean`. -/

namespace Connection

/-! ## Balances: `moveN` and the address bijection -/

theorem moveN_other (B : Pubkey → ℕ) {u v k : Pubkey} (n : ℕ) (hu : k ≠ u) (hv : k ≠ v) :
    moveN B u v n k = B k := by
  simp [moveN, Function.update_of_ne hu, Function.update_of_ne hv]

theorem moveN_congr {B B' : Pubkey → ℕ} {R : Pubkey → Prop} (hBB : ∀ j, R j → B j = B' j)
    {u v : Pubkey} (hu : R u) (hv : R v) (n : ℕ) : ∀ j, R j → moveN B u v n j = moveN B' u v n j := by
  intro j hj
  simp only [moveN, Function.update]
  by_cases h1 : j = v <;> by_cases h2 : j = u <;> by_cases h3 : v = u <;>
    simp [h1, h2, h3, hBB u hu, hBB v hv, hBB j hj]

theorem leBytes32_leNat (l : List U8) (hl : l.length = 32) : leBytes32 (leNatOfList l) = l := by
  have hlt : leNatOfList l < 256 ^ 32 := by have := leNatOfList_lt l; rwa [hl] at this
  apply toBytes_inj
  have h1 := natToBytesLE_leNat (leBytes32 (leNatOfList l))
  have h2 := natToBytesLE_leNat l
  rw [PrivacyCash.Proofs.G1.leBytes32_length, PrivacyCash.Proofs.G1.leNat_leBytes32 _ hlt] at h1
  rw [hl] at h2
  rw [← h1, ← h2]

theorem fromPubkey_toPubkey (k : Pubkey) : fromPubkey (toPubkey k) = k := by
  have hl : k.val.length = 32 := by simp
  have hlt : leNatOfList k.val < 2 ^ 256 := by
    have := leNatOfList_lt k.val; rw [hl] at this; simpa using this
  apply (Std.Array.eq_iff _ _).mpr
  simp only [fromPubkey, toPubkey, Std.Array.from_val, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  exact leBytes32_leNat _ hl

theorem toPubkey_fromPubkey (x : LeanSpec.Pubkey) : toPubkey (fromPubkey x) = x := by
  have hlt : x.toNat < 256 ^ 32 := by have := x.isLt; simpa using this
  apply BitVec.eq_of_toNat_eq
  simp only [toPubkey, fromPubkey, Std.Array.from_val, PrivacyCash.Proofs.G1.leNat_leBytes32 _ hlt,
    BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt x.isLt

theorem toPubkey_inj {k k' : Pubkey} (h : toPubkey k = toPubkey k') : k = k' := by
  rw [← fromPubkey_toPubkey k, h, fromPubkey_toPubkey]

theorem update_fromPubkey (B : Pubkey → ℕ) (u : Pubkey) (w : ℕ) :
    (fun x => Function.update B u w (fromPubkey x))
      = Function.update (fun x => B (fromPubkey x)) (toPubkey u) w := by
  funext x
  by_cases h : x = toPubkey u
  · subst h; simp [fromPubkey_toPubkey]
  · have : fromPubkey x ≠ u := fun e => h (by rw [← e, toPubkey_fromPubkey])
    simp [Function.update_of_ne h, Function.update_of_ne this]

theorem moveLamports_fromPubkey (B : Pubkey → ℕ) (u v : Pubkey) (n : ℕ) :
    LeanSpec.moveLamports (fun x => B (fromPubkey x)) (toPubkey u) (toPubkey v) n
      = fun x => moveN B u v n (fromPubkey x) := by
  have := congrFun (update_fromPubkey B u (B u - n)) (toPubkey v)
  simp only [fromPubkey_toPubkey] at this
  simp only [LeanSpec.moveLamports, moveN, fromPubkey_toPubkey]
  rw [← this, update_fromPubkey, update_fromPubkey]

/-! ## Small facts for the preconditions -/

theorem natOfLE_toBytes (l : List U8) :
    LeanSpec.natOfLE (toBytes l) = l.foldr (fun x acc => acc * 256 + x.val) 0 := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [toBytes, List.map_cons, LeanSpec.natOfLE, List.foldr_cons] at ih ⊢
    rw [ih]; simp; ring

theorem toBytes_toSlice (bs : LeanSpec.Bytes) (h : bs.length ≤ Usize.max) :
    toBytes (toSlice bs).val = bs := by
  have h' : (bs.map (fun b => (⟨b⟩ : U8))).length ≤ Usize.max := by simpa using h
  simp only [toSlice, dif_pos h', Slice.from_val, toBytes, List.map_map]
  conv_rhs => rw [← List.map_id bs]
  rfl

theorem serLength [LeanSpec.Groups] (inputs : LeanSpec.TxInputs) :
    (LeanSpec.serealizeExternalData inputs).length = 120 + inputs.encOut0.length + inputs.encOut1.length := by
  simp [LeanSpec.serealizeExternalData, LeanSpec.PubkeyToBytes, LeanSpec.i64LE, LeanSpec.u64LE,
    LeanSpec.vecU8, LeanSpec.u32LE, LeanSpec.natToBytesLE]
  omega

theorem publicBalance_of {s : State} {k : Pubkey} (h : ∀ b, (s k).data ≠ .nullifier b) :
    publicBalance s k = (s k).lamports.val := by
  unfold publicBalance; split
  · rename_i b hb; exact absurd hb (h b)
  · rfl

theorem ofResult_ok {α : Type} {r : Result α} {x : α} (h : ofResult r = .ok x) : r = ok x := by
  unfold ofResult at h
  cases r with
  | ret a =>
    simp [Option.ofResult] at h
    rw [h]
  | vis e k => simp [Option.ofResult] at h
  | div => simp [Option.ofResult] at h

/-- Anchor `init` at an address holding no lamports: a system transfer of the rent from the
    payer, then the account becomes the program's, with the given data. -/
theorem initAccount_empty {pid : Pubkey} {s s' : State} {mb : Nat → U64} {payer key : Pubkey}
    {space : Nat} {data : AccountData} (hzero : (s key).lamports.val = 0)
    (h : s.initAccount pid mb payer key space data = some s') :
    (s payer).owner = systemProgram ∧ (s payer).data.isEmpty ∧ (mb space).val ≤ (s payer).lamports.val ∧
      (fun k => (s' k).lamports.val) = moveN (fun k => (s k).lamports.val) payer key (mb space).val ∧
      (s' key).owner = pid ∧ (s' key).data = data ∧
      (∀ k, k ≠ key → (s' k).owner = (s k).owner ∧ (s' k).data = (s k).data) := by
  unfold State.initAccount at h
  simp only [hzero, if_true] at h
  cases hb : systemTransferBalances s s.balances payer key (mb space) with
  | none => simp [State.systemTransfer, hb] at h
  | some b =>
  simp only [State.systemTransfer, hb, Option.map_some, Option.some.injEq] at h
  subst h
  obtain ⟨ho, hd, hle, hv⟩ := stb_spec hb
  refine ⟨ho, hd, hle, ?_, by simp, by simp, fun k hk => by simp [State.set, hk]⟩
  funext k
  have := congrFun hv k
  by_cases hk : k = key
  · subst hk; simp [State.set, State.withBalances]; exact this
  · simp [State.set, hk, State.withBalances]; exact this

/-- What a successful `execTransact` consists of. -/
theorem execTransact_ok {d : Deployment} {s s' : State} {tx : TxEnv} {a : TransactAccounts}
    {proof : zkcash_core.transact.Proof} {ext : I64} {fee : U64} {out1 out2 : Slice U8}
    {evs : List CommitmentData}
    (h : execTransact d s tx a proof ext fee out1 out2 = .ok (s', evs)) :
    ∃ (tree : zkcash_core.merkle_tree.MerkleTreeAccount) (tt : zkcash_core.admin.TreeTokenAccount)
      (config : zkcash_core.admin.GlobalConfig) (mb : Nat → U64) (s₁ : State) (env' : SolEnv)
      (tree' : zkcash_core.merkle_tree.MerkleTreeAccount) (ap : zkcash_core.transact.Appended),
      TransactAccountsValid d.toAddresses s tx.toTxContext a proof.input_nullifiers.val[0]!
        proof.input_nullifiers.val[1]! tree tt config ∧
      tx.minimumBalance = some mb ∧
      (s.initAccount d.programId mb a.signer a.nullifier0 nullifierAccountSpace (.nullifier 0#u8)).bind
        (·.initAccount d.programId mb a.signer a.nullifier1 nullifierAccountSpace (.nullifier 0#u8)) = some s₁ ∧
      zkcash_core.transact.transact d.crypto.hasher arkFr d.crypto.sha256 d.crypto.proofVerifier solRuntime
        { accounts := s₁, balances := s₁.balances, signer := a.signer, treeToken := a.treeTokenAccount,
          recipient := a.recipient, feeRecipient := a.feeRecipientAccount,
          rentExemptMinimum := some (mb treeTokenAccountSpace) }
        tree config proof ext fee a.recipient a.feeRecipientAccount out1 out2 = ok (.Ok ap, env', tree') ∧
      s' = (s₁.withBalances env'.balances).set a.treeAccount
        { (s₁.withBalances env'.balances) a.treeAccount with data := .treeAccount tree' } := by
  unfold execTransact at h
  split at h
  swap; · simp at h
  rename_i tree tt config htree htt hconfig
  split at h
  · simp at h
  rename_i mb hmb
  split at h
  · simp at h
  rename_i s₁ hs₁
  dsimp only at h
  split at h
  · simp at h
  rename_i hvalid
  obtain ⟨⟨r, env', tree'⟩, hres, h⟩ := PrivacyCash.Model.Except.bind_ok h
  cases r with
  | Err e => cases h
  | Ok ap =>
  obtain ⟨s₄, hbal, h⟩ := PrivacyCash.Model.Except.bind_ok h
  cases h
  refine ⟨tree, tt, config, mb, s₁, env', tree', ap, not_not.mp hvalid, hmb, hs₁, ofResult_ok hres, ?_⟩
  rw [PrivacyCash.Model.checkBalanced_ok hbal]

variable [LeanSpec.PoseidonHashes] [LeanSpec.Sha] [LeanSpec.Groups]
  [AddCommGroup LeanSpec.G1] [Module LeanSpec.F LeanSpec.G1] [AddCommGroup LeanSpec.G2]
  [Module LeanSpec.F LeanSpec.G2] [CommGroup LeanSpec.GT] [LeanSpec.Pairing] [LeanSpec.Deployment]

theorem transact_refines
    {d : Deployment} {rent : Nat → U64} {spent : Finset LeanSpec.F} {s s' : State} {tx : TxEnv}
    {a : TransactAccounts} {proof : zkcash_core.transact.Proof} {extAmount : I64} {fee : U64}
    {out1 out2 : Slice U8} {events : List CommitmentData} (π : LeanSpec.Groth16.Proof)
    (hstep : step d s tx (.transact a proof extAmount fee out1 out2) = .ok (s', events))
    (hashes : HashesAgree d.crypto)
    (wf : WellFormed d spent s)
    (trusted : Trusted d rent tx proof out1 out2)
    (findings : Findings d rent s a proof extAmount fee)
    (hProofValid : d.crypto.proofVerifier.verify proof = ok true →
      LeanSpec.proofValid (toInputs a proof extAmount fee out1 out2 π)) :
    let inputs := toInputs a proof extAmount fee out1 out2 π
    let spent' := spent ∪ {inputs.k0, inputs.k1}
    LeanSpec.transact inputs (toWorld d rent spent s) (toWorld d rent spent' s') ∧
      WellFormed d spent' s' := by
  intro inputs spent'
  have hx : execTransact d s tx a proof extAmount fee out1 out2 = .ok (s', events) := hstep
  obtain ⟨tree, tt, config, mb, s₁, env', tree', ap, hvalid, hmb, hs₁, hhandler, hs'⟩ := execTransact_ok hx
  have hmbr : rent = mb := by rw [trusted.rentFixed] at hmb; exact Option.some.inj hmb
  subst hmbr
  -- the program's accounts are the canonical ones
  obtain ⟨htreeAddr, hshape⟩ := wf.tree _ _ hvalid.treeAccount.1
  have hpoolAddr := wf.pool _ _ hvalid.treeTokenAccount.1
  obtain ⟨hcfgAddr, hdr, hwr, hmr⟩ := wf.config _ _ hvalid.globalConfig.1
  -- the nullifier accounts
  set n0 := proof.input_nullifiers.val[0]! with hn0
  set n1 := proof.input_nullifiers.val[1]! with hn1
  have hnf0 : a.nullifier0 = d.pda (nullifier0Seeds n0) := hvalid.nullifier0.1
  have hnf1 : a.nullifier1 = d.pda (nullifier1Seeds n1) := hvalid.nullifier1.1
  have hnf01 : a.nullifier0 ≠ a.nullifier1 := by
    rw [hnf0, hnf1]; exact nullifier0_ne_nullifier1 trusted.nullifierAddressesDiffer
  have hz0 : (s a.nullifier0).lamports.val = 0 := by rw [hnf0]; exact findings.f2_nullifierAddressesEmpty.1
  have hz1 : (s a.nullifier1).lamports.val = 0 := by rw [hnf1]; exact findings.f2_nullifierAddressesEmpty.2
  have hnr := trusted.nullifierRentPositive
  set nr := (rent nullifierAccountSpace).val with hnrdef
  -- the two `init`s
  obtain ⟨sA, hA1, hA2⟩ := Option.bind_eq_some_iff.mp hs₁
  obtain ⟨hso, hsd, hsle, hlamA, hownA, hdataA, hotherA⟩ := initAccount_empty hz0 hA1
  have hs_nf0 : a.signer ≠ a.nullifier0 := fun e => by rw [e] at hsle; omega
  have hs_nf1 : a.signer ≠ a.nullifier1 := fun e => by rw [e] at hsle; omega
  have hzA : (sA a.nullifier1).lamports.val = 0 := by
    have := congrFun hlamA a.nullifier1
    rw [moveN_other _ _ (Ne.symm hs_nf1) (Ne.symm hnf01)] at this; rw [this, hz1]
  obtain ⟨hsoA, hsdA, hsleA, hlam1, hown1, hdata1, hother1⟩ := initAccount_empty hzA hA2
  have hsA : (sA a.signer).lamports.val = (s a.signer).lamports.val - nr := by
    have := congrFun hlamA a.signer
    simp only [moveN, Function.update_of_ne hs_nf0, Function.update_self] at this; exact this
  -- lamports after the two inits
  have hW₁ : (fun k => (s₁ k).lamports.val)
      = moveN (moveN (fun k => (s k).lamports.val) a.signer a.nullifier0 nr) a.signer a.nullifier1 nr := by
    rw [hlam1, hlamA]
  -- owners and data after the two inits
  have hod₁ : ∀ k, k ≠ a.nullifier0 → k ≠ a.nullifier1 → (s₁ k).owner = (s k).owner ∧ (s₁ k).data = (s k).data := by
    intro k h0 h1
    obtain ⟨o1, d1⟩ := hother1 k h1; obtain ⟨o0, d0⟩ := hotherA k h0
    exact ⟨o1.trans o0, d1.trans d0⟩
  have hnf0₁ : (s₁ a.nullifier0).owner = d.programId ∧ (s₁ a.nullifier0).data = .nullifier 0#u8 := by
    obtain ⟨o1, d1⟩ := hother1 _ hnf01; exact ⟨o1.trans hownA, d1.trans hdataA⟩
  have hnf1₁ : (s₁ a.nullifier1).owner = d.programId ∧ (s₁ a.nullifier1).data = .nullifier 0#u8 :=
    ⟨hown1, hdata1⟩
  -- the handler
  have hArec : a.recipient ≠ a.treeTokenAccount := by rw [hpoolAddr]; exact findings.f3_payeesNotPool.1
  have hTfee : a.feeRecipientAccount ≠ a.treeTokenAccount := by rw [hpoolAddr]; exact findings.f3_payeesNotPool.2
  have hok := handler_ok d.crypto _ tree config proof extAmount fee a.recipient a.feeRecipientAccount out1 out2
    ap env' tree' hArec hTfee hhandler
  -- the verifier: canonical public inputs
  have hcan := verifyProof_canonical _ proof _ hok.verify
  have hcanR : Canonical proof.root := by simpa [publicInputs] using hcan 0 (by decide)
  have hcan0 : Canonical n0 := by simpa [publicInputs, hn0] using hcan 3 (by decide)
  have hcan1 : Canonical n1 := by simpa [publicInputs, hn1] using hcan 4 (by decide)
  -- what the old world reads
  have htreeAt : treeAt s (treeAddr d) = tree := by
    simp only [treeAt, ← htreeAddr, hvalid.treeAccount.1.2]
  have hcfgAt : configAt s (configAddr d) = config := by
    simp only [configAt, ← hcfgAddr, hvalid.globalConfig.1.2]
  have hpoolData : (s a.treeTokenAccount).data = .treeToken tt := hvalid.treeTokenAccount.1.2
  have hpoolOwner : (s a.treeTokenAccount).owner = d.programId := hvalid.treeTokenAccount.1.1
  have hsigNotPool : a.signer ≠ a.treeTokenAccount := fun e => wf.programNotSystem (by
    rw [← hpoolOwner, ← e]; exact hso)
  have hnf0Init : Initializable s a.nullifier0 := hvalid.nullifier0.2
  have hnf1Init : Initializable s a.nullifier1 := hvalid.nullifier1.2
  have hpool_nf0 : a.treeTokenAccount ≠ a.nullifier0 := fun e => wf.programNotSystem (by
    rw [← hpoolOwner, e]; exact hnf0Init.1)
  have hpool_nf1 : a.treeTokenAccount ≠ a.nullifier1 := fun e => wf.programNotSystem (by
    rw [← hpoolOwner, e]; exact hnf1Init.1)
  have hW₁pool : (s₁ a.treeTokenAccount).lamports.val = (s a.treeTokenAccount).lamports.val := by
    rw [show (s₁ a.treeTokenAccount).lamports.val = _ from congrFun hW₁ a.treeTokenAccount,
      moveN_other _ _ (Ne.symm hsigNotPool) hpool_nf1, moveN_other _ _ (Ne.symm hsigNotPool) hpool_nf0]
  have hW₁sig : (s₁ a.signer).lamports.val = (s a.signer).lamports.val - nr - nr := by
    rw [show (s₁ a.signer).lamports.val = _ from congrFun hW₁ a.signer]
    simp only [moveN, Function.update_of_ne hs_nf1, Function.update_of_ne hs_nf0, Function.update_self]
  obtain ⟨v, hv, hdep, hwd⟩ := hok.rent
  have hvr : v = rent treeTokenAccountSpace := (Option.some.inj hv).symm
  subst hvr
  have hpub : LeanSpec.pubAmtConsistent extAmount.val fee.val (toF proof.public_amount) := by
    have := (checkPublicAmount_eq extAmount fee proof.public_amount).symm.trans hok.pubAmt
    simpa using this
  have hext0 : extAmount.val ≠ 0 := fun h0 => by have := hpub.2.1 (by omega); omega
  -- the two appends
  obtain ⟨p1, p2, t1, hap1, hap2⟩ := hok.appends
  obtain ⟨hT1, hsh1, hroom1, hidx1, -, hmax1, -⟩ := append_ok' d.crypto hashes _ tree t1 p1 hshape hap1
  obtain ⟨hT2, hsh2, hroom2, -, -, hmax2, -⟩ := append_ok' d.crypto hashes _ t1 tree' p2 hsh1 hap2
  -- external data
  obtain ⟨hsh, hcalc, hEq⟩ := hok.extHash
  have hcalc' := (extDataHash_eq d.crypto.sha256 a.recipient a.feeRecipientAccount
    zkcash_core.transact.SOL_ADDRESS extAmount out1 out2 fee inputs rfl rfl rfl rfl rfl rfl rfl
    trusted.fitsInVector).symm.trans hcalc
  have hfits : LeanSpec.encOutsFit inputs := by
    by_contra hn; rw [if_neg hn] at hcalc'; have := Result.ok_injective hcalc'; simp at this
  rw [if_pos hfits] at hcalc'
  obtain ⟨hsh', hsha, hcalc'⟩ := bindOk hcalc'
  have hshe : hsh' = hsh := Option.some.inj (Result.ok_injective hcalc')
  subst hshe
  have hser : LeanSpec.externalDataHash inputs = inputs.extDataHash := by
    have hb := hashes.sha256 _ _ hsha
    have hlen : (LeanSpec.serealizeExternalData inputs).length ≤ Usize.max := by
      rw [serLength]
      have : inputs.encOut0.length + inputs.encOut1.length = out1.length + out2.length := by
        simp [inputs, toInputs, toBytes, Slice.length]
      have := trusted.fitsInVector; omega
    rw [toBytes_toSlice _ hlen] at hb
    simp only [LeanSpec.externalDataHash, ← hb, natOfLE_toBytes]
    exact hEq
  -- balances the old world reads
  have hbalPool : (toWorld d rent spent s).poolBalance = (s a.treeTokenAccount).lamports.val := by
    simp only [LeanSpec.World.poolBalance, toWorld, fromPubkey_toPubkey, ← hpoolAddr]
    exact publicBalance_of (by rw [hpoolData]; intro b h; cases h)
  have hbalSig : (toWorld d rent spent s).balances inputs.s = (s a.signer).lamports.val := by
    simp only [toWorld, inputs, toInputs, fromPubkey_toPubkey]
    exact publicBalance_of (fun b h => by
      have := hsd; rw [h] at this; simp [AccountData.isEmpty] at this)
  have hbounds := i64_bounds extAmount
  have hfeeb : fee.val < 2 ^ 64 := by scalar_tac
  -- the preconditions
  have hpre : LeanSpec.transactPreconditions inputs (toWorld d rent spent s) := by
    refine ⟨?knownRoot, hser, ?minimumFee, hpub, hProofValid hok.verify, ?fresh, ?distinct,
      ?depositLimit, ?poolSolvency, ?signerSolvency, ?room, ?range, hfits, ?separate⟩
    case knownRoot =>
      show LeanSpec.rootKnown (toTree (treeAt s (treeAddr d))) (toF proof.root)
      rw [htreeAt]; exact isKnownRoot_safe tree proof.root hshape hcanR hok.root
    case minimumFee =>
      show LeanSpec.feeSufficient (toConfig (configAt s (configAddr d)) (treeAt s (treeAddr d))) _ _
      rw [hcfgAt, htreeAt]
      exact ((validateFee_iff extAmount fee config tree hdr hwr hmr).mp hok.feeOk).2
    case fresh =>
      have key : ∀ (n : Pubkey), Canonical n →
          (s (d.pda (nullifier0Seeds n))).owner ≠ d.programId →
          (s (d.pda (nullifier1Seeds n))).owner ≠ d.programId → toF n ∉ spent := by
        intro n hn h0 h1 hmem
        obtain ⟨m, hm, hmn, hown⟩ := wf.spentRecorded _ hmem
        obtain rfl := toF_injOn hm hn hmn
        rcases hown with h | h
        · exact h0 h
        · exact h1 h
      have sysNot : ∀ k, (s k).owner = systemProgram → (s k).owner ≠ d.programId :=
        fun k h e => wf.programNotSystem (e ▸ h)
      refine ⟨key n0 hcan0 ?_ ?_, key n1 hcan1 ?_ ?_⟩
      · rw [← hnf0]; exact sysNot _ hnf0Init.1
      · rw [← hvalid.nullifier3.1]; exact sysNot _ hvalid.nullifier3.2
      · rw [← hvalid.nullifier2.1]; exact sysNot _ hvalid.nullifier2.2
      · rw [← hnf1]; exact sysNot _ hnf1Init.1
    case distinct =>
      show toF n0 ≠ toF n1
      exact fun h => trusted.distinctNullifiers (toF_injOn hcan0 hcan1 h)
    case depositLimit =>
      show extAmount.val > 0 → extAmount.val ≤ ((toConfig (configAt s (configAddr d)) (treeAt s (treeAddr d))).maxDepositLimit : ℤ)
      rw [hcfgAt, htreeAt]; intro hp
      have := hok.depositLimit hp; simpa [toConfig] using this
    case poolSolvency =>
      rw [hbalPool]
      refine ⟨fun hn => ?_, fun ⟨hp, hf⟩ => ?_⟩
      · obtain ⟨hpoolv, -⟩ := hwd hn
        have h2 : (s₁ a.treeTokenAccount).lamports.val ≥ extAmount.val.natAbs + fee.val + (rent treeTokenAccountSpace).val := hpoolv
        rw [hW₁pool] at h2
        show ((s a.treeTokenAccount).lamports.val : ℤ) ≥ |inputs.extAmt| + (inputs.f : ℤ) + ((rent treeTokenAccountSpace).val : ℤ)
        have h1 : ((extAmount.val.natAbs : ℕ) : ℤ) = |extAmount.val| := Int.natCast_natAbs _
        show ((s a.treeTokenAccount).lamports.val : ℤ) ≥ |extAmount.val| + (fee.val : ℤ) + ((rent treeTokenAccountSpace).val : ℤ)
        omega
      · have hp' : extAmount.val ≥ 0 := hp
        have hpos : extAmount.val > 0 := by omega
        have := findings.f1_poolCoversFeeBeforeDeposit hpos (by exact_mod_cast hf)
        rw [hpoolAddr]; exact_mod_cast this
    case signerSolvency =>
      show (toWorld d rent spent s).balances inputs.s ≥ 2 * nr + _
      rw [hbalSig]
      have h1 : nr ≤ (s a.signer).lamports.val := hsle
      have h2 : nr ≤ (sA a.signer).lamports.val := hsleA
      split
      · rename_i hp
        obtain ⟨-, -, hle, -, -⟩ := hdep hp
        have hle' : extAmount.val ≤ (((s₁ a.signer).lamports.val : ℕ) : ℤ) := hle
        rw [hW₁sig] at hle'
        have hp' : extAmount.val > 0 := hp
        show (s a.signer).lamports.val ≥ 2 * nr + extAmount.val.natAbs
        omega
      · omega
    case room =>
      show (toTree (treeAt s (treeAddr d))).nextIndex ≤ 2 ^ 26 - 2
      rw [htreeAt]; simp only [toTree]; omega
    case range =>
      exact ⟨hbounds.1, hbounds.2, hfeeb⟩
    case separate =>
      refine ⟨fun e => hsigNotPool (by rw [hpoolAddr]; exact toPubkey_inj e), fun e => ?_, fun e => ?_⟩
      · exact findings.f3_payeesNotPool.1 (toPubkey_inj e)
      · exact findings.f3_payeesNotPool.2 (toPubkey_inj e)
  -- the new state, account by account
  have hs'k : ∀ k, (s' k).lamports = env'.balances k ∧ (s' k).owner = (s₁ k).owner ∧
      (s' k).data = (if k = a.treeAccount then .treeAccount tree' else (s₁ k).data) := by
    intro k; rw [hs']
    by_cases hk : k = a.treeAccount
    · subst hk; simp [State.set, State.withBalances]
    · simp [State.set, hk, State.withBalances]
  have htree_nf0 : a.treeAccount ≠ a.nullifier0 := fun e => wf.programNotSystem (by
    rw [← hvalid.treeAccount.1.1, e]; exact hnf0Init.1)
  have htree_nf1 : a.treeAccount ≠ a.nullifier1 := fun e => wf.programNotSystem (by
    rw [← hvalid.treeAccount.1.1, e]; exact hnf1Init.1)
  have hcfgOwner : (s a.globalConfig).owner = d.programId := hvalid.globalConfig.1.1
  have hcfg_nf0 : a.globalConfig ≠ a.nullifier0 := fun e => wf.programNotSystem (by
    rw [← hcfgOwner, e]; exact hnf0Init.1)
  have hcfg_nf1 : a.globalConfig ≠ a.nullifier1 := fun e => wf.programNotSystem (by
    rw [← hcfgOwner, e]; exact hnf1Init.1)
  have hcfg_tree : a.globalConfig ≠ a.treeAccount := fun e => by
    have h1 := hvalid.globalConfig.1.2; have h2 := hvalid.treeAccount.1.2
    rw [e, h2] at h1; cases h1
  have htreeAt' : treeAt s' (treeAddr d) = tree' := by
    simp only [treeAt, ← htreeAddr, (hs'k a.treeAccount).2.2, if_true]
  have hcfgAt' : configAt s' (configAddr d) = config := by
    simp only [configAt, ← hcfgAddr, (hs'k a.globalConfig).2.2, if_neg hcfg_tree,
      (hod₁ _ hcfg_nf0 hcfg_nf1).2, hvalid.globalConfig.1.2]
  -- BALANCES, on code addresses
  set P := publicBalance s with hPdef
  set Q := Function.update P a.signer (P a.signer - 2 * nr) with hQdef
  set Teff : (Pubkey → ℕ) → (Pubkey → ℕ) := fun B =>
    if extAmount.val > 0 then moveN B a.signer a.treeTokenAccount extAmount.val.natAbs
    else moveN B a.treeTokenAccount a.recipient extAmount.val.natAbs with hTdef
  have hcode : (fun k => (env'.balances k).val)
      = moveN (Teff (fun k => (s₁ k).lamports.val)) a.treeTokenAccount a.feeRecipientAccount fee.val := by
    by_cases hp : extAmount.val > 0
    · rw [(hdep hp).2.2.2.2]; simp only [hTdef, if_pos hp]; rfl
    · have hn : extAmount.val < 0 := by omega
      rw [(hwd hn).2]; simp only [hTdef, if_neg hp]; rfl
  have hsigData : ∀ b, (s a.signer).data ≠ .nullifier b := fun b h => by
    have := hsd; rw [h] at this; simp [AccountData.isEmpty] at this
  have hpoolDataN : ∀ b, (s a.treeTokenAccount).data ≠ .nullifier b := by
    rw [hpoolData]; intro b h; cases h
  obtain ⟨hrecN, hfeeN, hrec0', hrec1', hfee0', hfee1'⟩ := findings.f4_payeesNotNullifierAccounts
  have hrec0 : a.recipient ≠ a.nullifier0 := by rw [hnf0]; exact hrec0'
  have hrec1 : a.recipient ≠ a.nullifier1 := by rw [hnf1]; exact hrec1'
  have hfee0 : a.feeRecipientAccount ≠ a.nullifier0 := by rw [hnf0]; exact hfee0'
  have hfee1 : a.feeRecipientAccount ≠ a.nullifier1 := by rw [hnf1]; exact hfee1'
  let R : Pubkey → Prop := fun j => j ≠ a.nullifier0 ∧ j ≠ a.nullifier1 ∧ ∀ b, (s j).data ≠ .nullifier b
  have hRs : R a.signer := ⟨hs_nf0, hs_nf1, hsigData⟩
  have hRp : R a.treeTokenAccount := ⟨hpool_nf0, hpool_nf1, hpoolDataN⟩
  have hRr : R a.recipient := ⟨hrec0, hrec1, hrecN⟩
  have hRf : R a.feeRecipientAccount := ⟨hfee0, hfee1, hfeeN⟩
  have hagree : ∀ j, R j → (s₁ j).lamports.val = Q j := by
    intro j ⟨h0, h1, hd⟩
    rw [show (s₁ j).lamports.val = _ from congrFun hW₁ j]
    by_cases hjs : j = a.signer
    · subst hjs
      simp only [hQdef, Function.update_self, moveN, Function.update_of_ne hs_nf1,
        Function.update_of_ne hs_nf0, hPdef, publicBalance_of hd]
      omega
    · rw [moveN_other _ _ hjs h1, moveN_other _ _ hjs h0]
      simp only [hQdef, Function.update_of_ne hjs, hPdef, publicBalance_of hd]
  have hTagree : ∀ j, R j → Teff (fun k => (s₁ k).lamports.val) j = Teff Q j := by
    intro j hj
    simp only [hTdef]
    split
    · exact moveN_congr hagree hRs hRp _ j hj
    · exact moveN_congr hagree hRp hRr _ j hj
  have hRTs : ∀ j, R j → moveN (Teff (fun k => (s₁ k).lamports.val)) a.treeTokenAccount a.feeRecipientAccount fee.val j
      = moveN (Teff Q) a.treeTokenAccount a.feeRecipientAccount fee.val j :=
    moveN_congr hTagree hRp hRf _
  have hbalCode : ∀ k, publicBalance s' k = moveN (Teff Q) a.treeTokenAccount a.feeRecipientAccount fee.val k := by
    intro k
    obtain ⟨hl', ho', hd'⟩ := hs'k k
    by_cases hk : R k
    · have hnotN : ∀ b, (s' k).data ≠ .nullifier b := by
        intro b h; rw [hd'] at h
        split at h
        · cases h
        · rw [(hod₁ k hk.1 hk.2.1).2] at h; exact hk.2.2 b h
      rw [publicBalance_of hnotN, hl', ← hRTs k hk]
      exact congrFun hcode k
    · -- a nullifier account (new or old): 0 on both sides
      have hks : k ≠ a.signer := fun e => hk (e ▸ hRs)
      have hkp : k ≠ a.treeTokenAccount := fun e => hk (e ▸ hRp)
      have hkr : k ≠ a.recipient := fun e => hk (e ▸ hRr)
      have hkf : k ≠ a.feeRecipientAccount := fun e => hk (e ▸ hRf)
      have hEff : moveN (Teff Q) a.treeTokenAccount a.feeRecipientAccount fee.val k = P k := by
        rw [moveN_other _ _ hkp hkf]
        simp only [hTdef]
        split
        · rw [moveN_other _ _ hks hkp]; simp only [hQdef, Function.update_of_ne hks]
        · rw [moveN_other _ _ hkp hkr]; simp only [hQdef, Function.update_of_ne hks]
      rw [hEff]
      have hk' : k = a.nullifier0 ∨ k = a.nullifier1 ∨ ∃ b, (s k).data = .nullifier b := by
        by_contra hc; push_neg at hc; exact hk ⟨hc.1, hc.2.1, hc.2.2⟩
      have hktree : k ≠ a.treeAccount := by
        intro e; subst e
        rcases hk' with h | h | ⟨b, h⟩
        · exact htree_nf0 h
        · exact htree_nf1 h
        · rw [hvalid.treeAccount.1.2] at h; cases h
      have hP'0 : publicBalance s' k = 0 := by
        unfold publicBalance; rw [hd', if_neg hktree]
        rcases hk' with h | h | ⟨b, h⟩
        · rw [h, hnf0₁.2]
        · rw [h, hnf1₁.2]
        · have hk0 : k ≠ a.nullifier0 := fun e => by rw [e, hnf0Init.2] at h; cases h
          have hk1 : k ≠ a.nullifier1 := fun e => by rw [e, hnf1Init.2] at h; cases h
          rw [(hod₁ k hk0 hk1).2, h]
      rw [hP'0]
      rcases hk' with h | h | ⟨b, h⟩
      · subst h; simp only [hPdef, publicBalance, hnf0Init.2]; exact hz0.symm
      · subst h; simp only [hPdef, publicBalance, hnf1Init.2]; exact hz1.symm
      · simp only [hPdef, publicBalance, h]
  -- BALANCES, on spec addresses
  have hspecBal : (LeanSpec.transactEffects inputs (toWorld d rent spent s)).balances
      = fun x => moveN (Teff Q) a.treeTokenAccount a.feeRecipientAccount fee.val (fromPubkey x) := by
    have hW : (toWorld d rent spent s).balances = fun x => P (fromPubkey x) := rfl
    have hpool : (toWorld d rent spent s).state.pool = toPubkey a.treeTokenAccount := by
      simp only [toWorld, hpoolAddr]
    have hnrW : (toWorld d rent spent s).nullifierRent = nr := rfl
    have hext' : inputs.extAmt ≠ 0 := hext0
    simp only [LeanSpec.transactEffects, LeanSpec.transferEffects, LeanSpec.nullifierRentEffects,
      if_neg hext', hW, hpool, hnrW]
    have hs : inputs.s = toPubkey a.signer := rfl
    have hA : inputs.A = toPubkey a.recipient := rfl
    have ht : inputs.t = toPubkey a.feeRecipientAccount := rfl
    have hf : inputs.f = fee.val := rfl
    have he : inputs.extAmt = extAmount.val := rfl
    rw [hs, hA, ht, hf, he, fromPubkey_toPubkey, ← update_fromPubkey]
    simp only [hTdef]
    split
    · rw [moveLamports_fromPubkey, moveLamports_fromPubkey]
    · rw [moveLamports_fromPubkey, moveLamports_fromPubkey]
  -- the effects
  have heff : LeanSpec.AgreesOnProgramEffects inputs (LeanSpec.transactEffects inputs (toWorld d rent spent s))
      (toWorld d rent spent' s') := by
    refine ⟨?tree, ?nulls, ?pool, ?config, ?rentEx, ?nrent, ?bal⟩
    case nulls =>
      simp only [LeanSpec.transactEffects, LeanSpec.transferEffects, LeanSpec.nullifierRentEffects,
        if_neg (show inputs.extAmt ≠ 0 from hext0)]
      rfl
    case rentEx =>
      simp only [LeanSpec.transactEffects, LeanSpec.transferEffects, LeanSpec.nullifierRentEffects,
        if_neg (show inputs.extAmt ≠ 0 from hext0)]
      rfl
    case nrent =>
      simp only [LeanSpec.transactEffects, LeanSpec.transferEffects, LeanSpec.nullifierRentEffects,
        if_neg (show inputs.extAmt ≠ 0 from hext0)]
      rfl
    case tree =>
      show toTree (treeAt s' (treeAddr d)) = _
      simp only [LeanSpec.transactEffects, LeanSpec.transferEffects, LeanSpec.nullifierRentEffects,
        if_neg (show inputs.extAmt ≠ 0 from hext0)]
      rw [htreeAt']
      show toTree tree' = LeanSpec.appendEffects (toF proof.output_commitments.val[1]!)
        (LeanSpec.appendEffects (toF proof.output_commitments.val[0]!) (toTree (treeAt s (treeAddr d))))
      rw [htreeAt, ← hT1, ← hT2]
    case pool =>
      simp only [LeanSpec.transactEffects, LeanSpec.transferEffects, LeanSpec.nullifierRentEffects,
        if_neg (show inputs.extAmt ≠ 0 from hext0)]
      rfl
    case config =>
      show toConfig (configAt s' (configAddr d)) (treeAt s' (treeAddr d)) = _
      simp only [LeanSpec.transactEffects, LeanSpec.transferEffects, LeanSpec.nullifierRentEffects,
        if_neg (show inputs.extAmt ≠ 0 from hext0)]
      show toConfig (configAt s' (configAddr d)) (treeAt s' (treeAddr d))
        = toConfig (configAt s (configAddr d)) (treeAt s (treeAddr d))
      rw [hcfgAt', htreeAt', hcfgAt, htreeAt]
      simp only [toConfig, hmax2, hmax1]
    case bal =>
      rw [hspecBal]
      funext x
      exact hbalCode (fromPubkey x)
  -- the new state is well-formed
  have hkeep := PrivacyCash.Model.execTransact_keepsOwned hx
  have hfromOld : ∀ k, k ≠ a.treeAccount → k ≠ a.nullifier0 → k ≠ a.nullifier1 →
      (s' k).owner = (s k).owner ∧ (s' k).data = (s k).data := by
    intro k ht h0 h1
    obtain ⟨-, ho', hd'⟩ := hs'k k
    rw [ho', hd', if_neg ht]; exact hod₁ k h0 h1
  have hnfData' : ∀ k, (k = a.nullifier0 ∨ k = a.nullifier1) → ∃ b, (s' k).data = .nullifier b := by
    rintro k (rfl | rfl)
    · exact ⟨_, by rw [(hs'k _).2.2, if_neg (Ne.symm htree_nf0), hnf0₁.2]⟩
    · exact ⟨_, by rw [(hs'k _).2.2, if_neg (Ne.symm htree_nf1), hnf1₁.2]⟩
  have hwf' : WellFormed d spent' s' := by
    refine ⟨wf.programNotSystem, ?_, ?_, ?_, ?_⟩
    · intro k t ⟨ho, hd⟩
      by_cases ht : k = a.treeAccount
      · subst ht
        rw [(hs'k _).2.2, if_pos rfl] at hd
        cases hd; exact ⟨htreeAddr, hsh2⟩
      by_cases h0 : k = a.nullifier0
      · obtain ⟨b, hb⟩ := hnfData' k (Or.inl h0); rw [hb] at hd; cases hd
      by_cases h1 : k = a.nullifier1
      · obtain ⟨b, hb⟩ := hnfData' k (Or.inr h1); rw [hb] at hd; cases hd
      obtain ⟨ho', hd'⟩ := hfromOld k ht h0 h1
      exact wf.tree k t ⟨by rw [← ho']; exact ho, by rw [← hd']; exact hd⟩
    · intro k p ⟨ho, hd⟩
      by_cases ht : k = a.treeAccount
      · subst ht; rw [(hs'k _).2.2, if_pos rfl] at hd; cases hd
      by_cases h0 : k = a.nullifier0
      · obtain ⟨b, hb⟩ := hnfData' k (Or.inl h0); rw [hb] at hd; cases hd
      by_cases h1 : k = a.nullifier1
      · obtain ⟨b, hb⟩ := hnfData' k (Or.inr h1); rw [hb] at hd; cases hd
      obtain ⟨ho', hd'⟩ := hfromOld k ht h0 h1
      exact wf.pool k p ⟨by rw [← ho']; exact ho, by rw [← hd']; exact hd⟩
    · intro k c ⟨ho, hd⟩
      by_cases ht : k = a.treeAccount
      · subst ht; rw [(hs'k _).2.2, if_pos rfl] at hd; cases hd
      by_cases h0 : k = a.nullifier0
      · obtain ⟨b, hb⟩ := hnfData' k (Or.inl h0); rw [hb] at hd; cases hd
      by_cases h1 : k = a.nullifier1
      · obtain ⟨b, hb⟩ := hnfData' k (Or.inr h1); rw [hb] at hd; cases hd
      obtain ⟨ho', hd'⟩ := hfromOld k ht h0 h1
      exact wf.config k c ⟨by rw [← ho']; exact ho, by rw [← hd']; exact hd⟩
    · intro x hx'
      rcases Finset.mem_union.mp hx' with hold | hnew
      · obtain ⟨n, hn, hnx, hown⟩ := wf.spentRecorded x hold
        exact ⟨n, hn, hnx, hown.imp (hkeep _) (hkeep _)⟩
      · rcases Finset.mem_insert.mp hnew with h | h
        · refine ⟨n0, hcan0, h.symm, Or.inl ?_⟩
          rw [← hnf0, (hs'k _).2.1]; exact hnf0₁.1
        · rw [Finset.mem_singleton] at h
          refine ⟨n1, hcan1, h.symm, Or.inr ?_⟩
          rw [← hnf1, (hs'k _).2.1]; exact hnf1₁.1
  exact ⟨⟨hpre, heff⟩, hwf'⟩

end Connection
