import Connection.Proofs.ToySpend
open Aeneas Aeneas.Std Result PrivacyCash.Model

/-! # Finding I1: `transact_connection` fails without `CircuitFacts`

`TransactConnectionWithoutCircuit` is `transact_connection`
(`Connection/ConnectionTheorems.lean`) with the hypothesis `CircuitFacts` (the circuit keeps an
accepted proof's two input nullifiers distinct) removed; every other hypothesis and the conclusion are unchanged. It is false
(`transact_connection_fails_without_circuit`): in the toy deployment, after `initialize` and
the toy deposit of 2 lamports, `step` accepts a withdrawal of those 2 lamports whose two input
nullifiers are equal (both `2`), every remaining hypothesis holds, and the spec's `transact` does
not (its precondition `nullifiersDistinct` fails). Neither the program nor Anchor checks that the
nullifiers differ: `nullifier2` and `nullifier3` get the addresses of `nullifier0` and
`nullifier1` themselves, and Anchor checks them (system accounts) before it creates those. -/

namespace Connection

section
variable {G1 G2 GT : Type} [AddCommGroup G1] [Module LeanSpec.F G1] [AddCommGroup G2]
  [Module LeanSpec.F G2] [CommGroup GT] [LeanSpec.PoseidonHashes] [LeanSpec.Sha]

/-- The conclusion of `transact_connection`: the spec's `transact` holds between the worlds
    before and after the accepted transaction. -/
def SpecTransactHolds (d : Deployment) (rent : Nat → U64) (C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT)
    (laws : PairingLaws C.e) (evs : List Event) (s s' : State) (tx : TxEnv) (a : TransactAccounts)
    (proof : zkcash_core.transact.Proof) (extAmount : I64) (fee : U64) (out1 out2 : Slice U8) : Prop :=
  letI : LeanSpec.Groups := syscallGroups C
  letI : LeanSpec.Pairing := syscallPairing C
  letI : LeanSpec.Deployment := ⟨programKey C⟩
  let inputs := toInputs tx.signers a proof extAmount fee out1 out2
  LeanSpec.transact inputs (toWorld d rent (runSpent evs) s)
    (toWorld d rent (runSpent evs ∪ {inputs.k0, inputs.k1}) s')

end

/-- `transact_connection` without `CircuitFacts`; all other hypotheses are kept. -/
def TransactConnectionWithoutCircuit : Prop :=
  ∀ (G1 G2 GT : Type) [AddCommGroup G1] [Module LeanSpec.F G1] [AddCommGroup G2]
    [Module LeanSpec.F G2] [CommGroup GT] [LeanSpec.PoseidonHashes] [LeanSpec.Sha]
    (d : Deployment) (rent : Nat → U64) (s₀ s s' : State) (evs : List Event) (tx : TxEnv)
    (a : TransactAccounts) (proof : zkcash_core.transact.Proof) (extAmount : I64) (fee : U64)
    (out1 out2 : Slice U8) (events : List CommitmentData)
    (C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT) (laws : PairingLaws C.e),
    Genesis d.programId s₀ →
    Run d s₀ evs s →
    DeploymentFacts d →
    Run d s [.program tx (.transact a proof extAmount fee out1 out2) events] s' →
    HashesAgree d.crypto →
    SolanaFacts d tx →
    CryptoFacts d proof →
    OutsideSpecDetail d rent s tx a proof →
    SpecTransactHolds d rent C laws evs s s' tx a proof extAmount fee out1 out2

namespace Toy
open zkcash_core
attribute [local instance] toyPoseidon toySpecSha

/-! ## The withdrawal with equal nullifiers -/

/-- The toy withdrawal (`spendProof`) with both input nullifiers `2`. -/
def dupProof : transact.Proof :=
  { spendProof with input_nullifiers := Std.Array.make 2#usize [two32, two32] (by simp) }

/-- It pays the note's 2 lamports to the recipient, with no fee (public amount `-2`, as
    `spendProof`). -/
def dupExt : I64 := (-2)#i64

theorem dupExt_val : dupExt.val = -2 := by simp [dupExt]

/-- Its accounts: `nullifier2` (slot 0, nullifier 1) is `nullifier0`'s address, `nullifier3`
    (slot 1, nullifier 0) is `nullifier1`'s. -/
def dupA : TransactAccounts :=
  { spendA with nullifier0 := nf0W, nullifier1 := nf3W, nullifier2 := nf0W, nullifier3 := nf3W }

/-- Toy addresses with different seed bytes at position 9 differ (`toyCPA` keeps that byte). -/
theorem toyCPA_byte9 {l l' : List U8} (h : toyCPA l = toyCPA l') : l.getD 9 0#u8 = l'.getD 9 0#u8 := by
  have := congrArg (fun a : Pubkey => a.val) h
  simp only [toyCPA, Std.Array.make] at this
  simp at this
  exact this.2.1

theorem dup_addr : nf0W ≠ nf3W ∧ pk 3#u8 ≠ nf3W ∧ pk 4#u8 ≠ nf3W := by
  refine ⟨fun h => ?_, ?_, ?_⟩
  · have := toyCPA_byte9 h
    revert this
    decide +kernel
  · unfold nf3W; decide +kernel
  · unfold nf3W; decide +kernel

/-- The spec's preconditions other than `distinctNullifiers` (`PreExceptDistinct`), in the
    handler's view, for the toy deployment. -/
def HandlerPreND (signers : List Pubkey) (a : TransactAccounts) (s₁ : State) (v : U64)
    (tree : merkle_tree.MerkleTreeAccount) (config : admin.GlobalConfig) (spent : Finset LeanSpec.F)
    (proof : transact.Proof) (ext : I64) (fee : U64) (out1 out2 : Slice U8) : Prop :=
  @PreExceptDistinct _ _ (syscallGroups toyC) (inferInstanceAs (AddCommGroup Unit))
    (inferInstanceAs (Module LeanSpec.F Unit))
    (inferInstanceAs (CommGroup Unit))
    (syscallPairing toyC) (@LeanSpec.Deployment.mk (syscallGroups toyC) (programKey toyC))
    (toInputs signers a proof ext fee out1 out2) (handlerWorld a s₁ v tree config spent)

/-- The spec's preconditions other than `distinctNullifiers` hold for the withdrawal (as
    `spend_pre`, with the split 2/0). -/
theorem dup_pre (sB : State) (tree₂ t1 : merkle_tree.MerkleTreeAccount) (config : admin.GlobalConfig)
    (c : LeanSpec.F) (htree : toTree tree₂ = LeanSpec.appendEffects c (toTree t1))
    (hTn : tree₂.next_index.val = 2) (hwr : config.withdrawal_fee_rate.val = 25)
    (hpoolB : (sB tokenA).lamports.val = 3) (hrecB : (sB (pk 3#u8)).lamports.val = 0) :
    HandlerPreND toyTx.signers dupA sB 1#u64 tree₂ config ∅ dupProof dupExt 0#u64 emptySlice emptySlice := by
  unfold HandlerPreND
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hTP, -⟩ := dep_addr
  have hdec := decode_toInputs (signers := toyTx.signers) toyC dupProof dupA dupExt 0#u64 emptySlice emptySlice
    toy_alpha_decodes rfl toy_zeros_decodes
  have he : (toInputs toyTx.signers dupA dupProof dupExt 0#u64 emptySlice emptySlice).extAmt = -2 := dupExt_val
  have hf : (toInputs toyTx.signers dupA dupProof dupExt 0#u64 emptySlice emptySlice).f = 0 := by simp [toInputs]
  have h3P : pk 3#u8 ≠ tokenA := by unfold tokenA; decide +kernel
  have h4P : pk 4#u8 ≠ tokenA := by unfold tokenA; decide +kernel
  have hpool : (handlerWorld dupA sB 1#u64 tree₂ config ∅).state.pool = toPubkey tokenA := rfl
  have hnr : (handlerWorld dupA sB 1#u64 tree₂ config ∅).nullifierRent = 0 := rfl
  have hA : (toInputs toyTx.signers dupA dupProof dupExt 0#u64 emptySlice emptySlice).A = toPubkey (pk 3#u8) := rfl
  have hs : (toInputs toyTx.signers dupA dupProof dupExt 0#u64 emptySlice emptySlice).s = toPubkey (pk 1#u8) := rfl
  have ht : (toInputs toyTx.signers dupA dupProof dupExt 0#u64 emptySlice emptySlice).t = toPubkey (pk 4#u8) := rfl
  have hpb : (handlerWorld dupA sB 1#u64 tree₂ config ∅).balances (toPubkey tokenA) = 3 := by
    show (sB (fromPubkey (toPubkey tokenA))).lamports.val = 3
    rw [fromPubkey_toPubkey, hpoolB]
  refine @PreExceptDistinct.mk _ _ (syscallGroups toyC) (inferInstanceAs (AddCommGroup Unit))
    (inferInstanceAs (Module LeanSpec.F Unit))
    (inferInstanceAs (CommGroup Unit))
    (syscallPairing toyC) (@LeanSpec.Deployment.mk (syscallGroups toyC) (programKey toyC)) _ _
    ?_ ?_ ?_ ?_ ⟨_, hdec, rfl⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- the root: the deposit's last append stored the root `1`
    show LeanSpec.rootBytesKnown (toTree tree₂) (toBytes one32.val)
    rw [rootBytesKnown_iff]
    refine ⟨canonical_one32, ⟨⟨(toTree t1).rootIndex + 1, ?_⟩, by rw [toF_one32]; decide⟩⟩
    rw [htree, toy_append_history, toF_one32]
  · show (LeanSpec.natOfLE (List.replicate 32 0) : LeanSpec.F) = toF zeros32
    rw [toF_zeros32]; rfl
  · unfold LeanSpec.feeSufficient; rw [he, hf]; simp [handlerWorld, toConfig, hwr]
  · unfold LeanSpec.pubAmtConsistent; rw [he, hf]
    refine ⟨fun h => by omega, ?_⟩
    show toF minusTwo32 = _; rw [toF_minusTwo32]; norm_num
  · simp [LeanSpec.nullifiersFresh, handlerWorld]
  · intro h; rw [he] at h; omega
  · unfold LeanSpec.poolSolvent; rw [he, hf]
    refine ⟨fun _ => ?_, fun h => by omega⟩
    have hpb' : (handlerWorld dupA sB 1#u64 tree₂ config ∅).poolBalance = 3 := hpb
    rw [hpb']; simp [handlerWorld]
  · unfold LeanSpec.signerSolvent; rw [he]; simp [handlerWorld]
  · exact List.mem_map_of_mem (f := toPubkey) (List.mem_singleton.mpr rfl)
  · show (toTree tree₂).nextIndex ≤ 2 ^ 26 - 2; simp [toTree, hTn]
  · unfold LeanSpec.amountsInRange; rw [he, hf]; norm_num
  · simp [LeanSpec.encOutsFit, toInputs, emptySlice, toBytes]
  · exact ⟨fun e => (Ne.symm hTP) (toPubkey_inj e), fun _ e => h3P (toPubkey_inj e),
      fun h => by rw [hf] at h; omega⟩
  · intro i
    show LeanSpec.canonicalEncoding (toBytes ((publicInputs _)[i.val]!).val) _
    rw [canonicalEncoding_iff]
    fin_cases i
    · exact ⟨canonical_one32, rfl⟩
    · exact ⟨canonical_minusTwo32, rfl⟩
    · exact ⟨canonical_zeros32, rfl⟩
    · exact ⟨canonical_two32, rfl⟩
    · exact ⟨canonical_two32, rfl⟩
    · exact ⟨canonical_zeros32, rfl⟩
    · exact ⟨canonical_zeros32, rfl⟩
  · refine ⟨fun k hk => ?_, fun h => by rw [he] at h; omega⟩
    -- only the recipient is credited, and it holds nothing
    unfold LeanSpec.balanceDelta at hk ⊢
    rw [he, hf, hpool, hnr, hA, hs, ht] at hk ⊢
    by_cases hk3 : k = toPubkey (pk 3#u8)
    · subst hk3
      have hb : (handlerWorld dupA sB 1#u64 tree₂ config ∅).balances (toPubkey (pk 3#u8)) = 0 := by
        show (sB (fromPubkey (toPubkey (pk 3#u8)))).lamports.val = 0
        rw [fromPubkey_toPubkey, hrecB]
      rw [hb]
      have h3p : toPubkey (pk 3#u8) ≠ toPubkey tokenA := fun e => h3P (toPubkey_inj e)
      simp only [h3p, if_false]
      split_ifs <;> norm_num
    · exfalso
      simp only [hk3, false_and, if_false] at hk
      split_ifs at hk <;> omega

/-- **The withdrawal with equal nullifiers is accepted by `step`** (as `toy_spend_ok`). -/
theorem toy_dup_ok (s₂ : State) (tree₂ t1 : merkle_tree.MerkleTreeAccount) (token : admin.TreeTokenAccount)
    (config : admin.GlobalConfig) (c : LeanSpec.F)
    (hT : s₂ treeA = ⟨1#u64, toyD.programId, .treeAccount tree₂⟩)
    (hK : s₂ tokenA = ⟨3#u64, toyD.programId, .treeToken token⟩)
    (hC : s₂ configA = ⟨1#u64, toyD.programId, .globalConfig config⟩)
    (hP : s₂ (pk 1#u8) = ⟨993#u64, systemProgram, .empty⟩)
    (hO : ∀ k, k ≠ treeA → k ≠ tokenA → k ≠ configA → k ≠ pk 1#u8 → k ≠ nf0A → k ≠ nf1A → s₂ k = toyS0 k)
    (hshape : TreeShape tree₂) (hroots : ∀ j : Fin 100, Canonical tree₂.root_history.val[j.val]!)
    (hsubs : ∀ j : Fin 26, Canonical tree₂.subtrees.val[j.val]!)
    (htree : toTree tree₂ = LeanSpec.appendEffects c (toTree t1)) (hTn : tree₂.next_index.val = 2)
    (hTb : tree₂.bump = 255#u8) (hkb : token.bump = 255#u8) (hcb : config.bump = 255#u8)
    (hdr : config.deposit_fee_rate.val = 0) (hwr : config.withdrawal_fee_rate.val = 25)
    (hmr : config.fee_error_margin.val = 500) :
    ∃ s' events, step toyD s₂ toyTx (.transact dupA dupProof dupExt 0#u64 emptySlice emptySlice)
      = .ok (s', events) := by
  obtain ⟨w01, w02, w03, w04, w05, w06, -, -, -, -, -, -, -, -, -, -, -, -, -,
    w11, w12, w13, w14, w15, w16, p30, -, -, -, p3a, p3b⟩ := spend_addr
  obtain ⟨w0n1, p31, -⟩ := dup_addr
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, p3T, p3K, p3C, -, -, -,
    -, -, -, -, hTP, -⟩ := dep_addr
  have p31' : pk 3#u8 ≠ pk 1#u8 := pk_ne (by decide)
  have h3P : pk 3#u8 ≠ tokenA := p3K
  have hPs : s₂ dupA.signer = ⟨993#u64, systemProgram, .empty⟩ := hP
  have hz : ∀ k, k ≠ treeA → k ≠ tokenA → k ≠ configA → k ≠ pk 1#u8 → k ≠ nf0A → k ≠ nf1A →
      (s₂ k).lamports.val = 0 ∧ (s₂ k).owner = systemProgram ∧ (s₂ k).data = .empty := by
    intro k e1 e2 e3 e4 e5 e6
    rw [hO k e1 e2 e3 e4 e5 e6]; unfold toyS0; rw [if_neg e4]; exact ⟨rfl, rfl, rfl⟩
  -- the two nullifier inits, paid by the signer
  obtain ⟨sA, hA, oA, dA, lA, -, -, -, kA, mA⟩ := init_step (pid := toyD.programId)
    (space := nullifierAccountSpace) (data := .nullifier 0#u8) (s := s₂) (payer := dupA.signer)
    (key := dupA.nullifier0) (hz nf0W w01 w02 w03 w04 w05 w06).1 (by rw [hPs]) (by rw [hPs]; rfl)
    (by rw [hPs]; decide) (Ne.symm w04)
  have z1 : (sA dupA.nullifier1).lamports.val = 0 := by
    rw [kA dupA.nullifier1 w14 (Ne.symm w0n1)]; exact (hz nf3W w11 w12 w13 w14 w15 w16).1
  have lA' : (sA dupA.signer).lamports.val = 992 := by rw [lA, hPs]; rfl
  obtain ⟨sB, hB, oB, dB, lB, -, -, -, kB, mB⟩ := init_step (pid := toyD.programId)
    (space := nullifierAccountSpace) (data := .nullifier 0#u8) (s := sA) (payer := dupA.signer)
    (key := dupA.nullifier1) z1 (by rw [oA, hPs]) (by rw [dA, hPs]; rfl) (by rw [lA']; omega) (Ne.symm w14)
  have hsB : ∀ k, k ≠ pk 1#u8 → k ≠ nf0W → k ≠ nf3W → sB k = s₂ k := fun k h1 h2 h3 =>
    (kB k h1 h3).trans (kA k h1 h2)
  have hpoolB : (sB tokenA).lamports.val = 3 := by
    rw [hsB tokenA hTP (Ne.symm w02) (Ne.symm w12), hK]; rfl
  have hrecB : (sB (pk 3#u8)).lamports.val = 0 := by
    rw [hsB _ p31' p30 p31]; exact (hz _ p3T p3K p3C p31' p3a p3b).1
  -- the handler, without distinct nullifiers
  obtain ⟨ap, env', tree', hh⟩ := handler_ok_exists_nd toyCrypto toyC toyLaws toyHashesAgree toyHashesSucceed
    toySyscalls toyKey dupA sB 1#u64 tree₂ config ∅ dupProof dupExt 0#u64 emptySlice emptySlice hshape
    hroots hsubs (by omega) (by omega) (by omega)
    ⟨by rw [oB, oA, hPs], by rw [dB, dA, hPs]; rfl⟩ toyFit (by rw [dupExt_val]; decide) alpha_ne_zeros
    (dup_pre sB tree₂ t1 config c htree hTn hwr hpoolB hrecB)
  -- lamports are conserved
  have hok := handler_ok toyCrypto _ _ _ _ _ _ _ _ _ _ _ _ _ hh
  obtain ⟨v', -, -, hwd, -⟩ := hok.rent
  have hneg : dupExt.val < 0 := by rw [dupExt_val]; decide
  have habs : dupExt.val.natAbs = 2 := by rw [dupExt_val]; rfl
  have he : (fun k => (env'.balances k).val) = payN (fun k => (sB k).lamports.val) dupA.treeTokenAccount
      dupA.recipient 2 := by
    have := (hwd hneg).2
    rw [habs, show (0#u64 : U64).val = 0 by simp, payN_zero] at this
    exact this
  set K := [dupA.treeAccount, dupA.nullifier0, dupA.nullifier1, dupA.nullifier2, dupA.nullifier3,
    dupA.treeTokenAccount, dupA.globalConfig, dupA.recipient, dupA.feeRecipientAccount, dupA.signer,
    dupA.systemProgram] with hK'
  have hTL : TL K (fun k => (env'.balances k).val) = TL K (fun k => (s₂ k).lamports.val) := by
    rw [he, TL_payN (by simp [hK']) (by simp [hK']) _ (by show 2 ≤ (sB tokenA).lamports.val; rw [hpoolB]; decide),
      if_neg (show dupA.recipient ≠ dupA.treeTokenAccount from h3P), add_zero,
      mB, TL_moveN (by simp [hK']) (by simp [hK']) _ (by show 1 ≤ (sA dupA.signer).lamports.val; omega),
      mA, TL_moveN (by simp [hK']) (by simp [hK']) _ (by show 1 ≤ (s₂ dupA.signer).lamports.val; rw [hPs]; decide)]
  -- the account checks: `nullifier2` is `nullifier0`, `nullifier3` is `nullifier1`, both still
  -- system accounts when Anchor checks them
  have hv : TransactAccountsValid toyD.toAddresses s₂ toyTx.toTxContext dupA dupProof.input_nullifiers.val[0]!
      dupProof.input_nullifiers.val[1]! tree₂ token config := by
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨⟨?_, ?_⟩, ?_⟩, ⟨⟨?_, ?_⟩, ?_⟩,
      by simp [dupA, spendA, toyTx], rfl⟩
    · show (s₂ treeA).owner = _; rw [hT]
    · show (s₂ treeA).data = _; rw [hT]
    · rw [hTb]; rfl
    · obtain ⟨-, h1, h2⟩ := hz nf0W w01 w02 w03 w04 w05 w06; exact ⟨h1, h2⟩
    · obtain ⟨-, h1, h2⟩ := hz nf3W w11 w12 w13 w14 w15 w16; exact ⟨h1, h2⟩
    · exact (hz nf0W w01 w02 w03 w04 w05 w06).2.1
    · exact (hz nf3W w11 w12 w13 w14 w15 w16).2.1
    · show (s₂ tokenA).owner = _; rw [hK]
    · show (s₂ tokenA).data = _; rw [hK]
    · rw [hkb]; rfl
    · show (s₂ configA).owner = _; rw [hC]
    · show (s₂ configA).data = _; rw [hC]
    · rw [hcb]; rfl
  obtain ⟨events, hex⟩ := execTransact_ok_of (by show (s₂ treeA).data = _; rw [hT])
    (by show (s₂ tokenA).data = _; rw [hK]) (by show (s₂ configA).data = _; rw [hC]) hv rfl
    (by rw [hA, Option.bind_some, hB]) hh hTL
  exact ⟨_, events, hex⟩

/-- The execution `initialize`, deposit, withdrawal with equal nullifiers: every step is
    accepted, and the withdrawal satisfies every hypothesis of
    `TransactConnectionWithoutCircuit` that is not about the execution. -/
theorem toy_dup_execution :
    ∃ (s₁ s₂ s₃ : State) (e₂ e₃ : List CommitmentData),
      step toyD toyS0 toyTx (.initialize toyInitA) = .ok (s₁, []) ∧
      step toyD s₁ toyTx (.transact depA depProof 2#i64 0#u64 emptySlice emptySlice) = .ok (s₂, e₂) ∧
      step toyD s₂ toyTx (.transact dupA dupProof dupExt 0#u64 emptySlice emptySlice) = .ok (s₃, e₃) ∧
      PdaCollisionFree toyD.toAddresses
        {toyD.pdaInput (nullifier0Seeds dupProof.input_nullifiers.val[0]!),
         toyD.pdaInput (nullifier1Seeds dupProof.input_nullifiers.val[1]!)} ∧
      OutsideSpecDetail toyD toyRent s₂ toyTx dupA dupProof := by
  obtain ⟨s₁, tree, token, config, hinit, hT, hK, hC, hP, hO, hshape, hroots, hsubs, hT0, hTn, hTb, hTm,
    hkb, hcb, hdr, hwr, hmr⟩ := toy_init_ok
  obtain ⟨s₂, e₂, tree₂, hstep₂, hT2, hK2, hC2, hP2, hO2, p1, p2, t1, hap1, hap2⟩ :=
    toy_deposit_ok s₁ tree token config hT hK hC hP hO hshape hroots hsubs hT0 hTn hTb
      (hTm ▸ default_limit_ge2) hkb hcb hdr hwr hmr
  have hinitStep : step toyD toyS0 toyTx (.initialize toyInitA) = .ok (s₁, []) := by
    show (do let s' ← execInitialize toyD toyS0 toyTx toyInitA; pure (s', [])) = _
    rw [hinit]; rfl
  obtain ⟨-, hsh1, -, hn1, -, -, hb1⟩ := append_ok' toyCrypto toyHashesAgree _ tree t1 p1 hshape hap1
  obtain ⟨htree, hsh2, -, hn2, -, -, hb2⟩ := append_ok' toyCrypto toyHashesAgree _ t1 tree₂ p2 hsh1 hap2
  have hrun₂ : Run toyD toyS0 [.program toyTx (.initialize toyInitA) [],
      .program toyTx (.transact depA depProof 2#i64 0#u64 emptySlice emptySlice) e₂] s₂ :=
    .program hinitStep toyTx_rentPositive (.program hstep₂ toyTx_rentPositive (.nil _))
  have hpid : toyD.programId ≠ systemProgram := by unfold toyD; decide +kernel
  have wf₂ := wf_reachable toyGenesis hrun₂ hpid toyHashesAgree
  have hold₂ : HoldsTree toyD.programId s₂ treeA tree₂ := by unfold HoldsTree; rw [hT2]; exact ⟨rfl, rfl⟩
  obtain ⟨s₃, e₃, hstep₃⟩ := toy_dup_ok s₂ tree₂ t1 token config _ hT2 hK2 hC2 hP2 hO2 hsh2
    (wf₂.storedRoots _ _ hold₂) (wf₂.storedSubtrees _ _ hold₂) htree (by rw [hn2, hn1, hTn]; rfl)
    (by rw [hb2, hb1, hTb]) hkb hcb hdr hwr hmr
  obtain ⟨w01, w02, w03, w04, w05, w06, -, -, -, -, -, -, -, -, -, -, -, -, -,
    w11, w12, w13, w14, w15, w16, p30, -, p40, -, p3a, p3b⟩ := spend_addr
  obtain ⟨w0n1, p31, p41⟩ := dup_addr
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, p3T, p3K, p3C, p4T, p4K, p4C,
    -, -, p4a, p4b, -, -⟩ := dep_addr
  have p31' : pk 3#u8 ≠ pk 1#u8 := pk_ne (by decide)
  have p41' : pk 4#u8 ≠ pk 1#u8 := pk_ne (by decide)
  refine ⟨s₁, s₂, s₃, e₂, e₃, hinitStep, hstep₂, hstep₃, ?_, ⟨rfl, ?_, ?_⟩⟩
  · intro x hx y hy hxy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rfl
    · exact absurd hxy w0n1
    · exact absurd hxy.symm w0n1
    · rfl
  · refine ⟨?_, ?_⟩
    · show (s₂ nf0W).lamports.val = 0
      rw [hO2 nf0W w01 w02 w03 w04 w05 w06]; unfold toyS0; decide +kernel
    · show (s₂ nf3W).lamports.val = 0
      rw [hO2 nf3W w11 w12 w13 w14 w15 w16]; unfold toyS0; decide +kernel
  · refine ⟨fun b h => ?_, fun b h => ?_, p30, p31, p40, p41⟩
    · rw [show s₂ dupA.recipient = toyS0 (pk 3#u8) from hO2 _ p3T p3K p3C p31' p3a p3b] at h
      unfold toyS0 at h; rw [if_neg p31'] at h; cases h
    · rw [show s₂ dupA.feeRecipientAccount = toyS0 (pk 4#u8) from hO2 _ p4T p4K p4C p41' p4a p4b] at h
      unfold toyS0 at h; rw [if_neg p41'] at h; cases h

end Toy

attribute [local instance] Toy.toyPoseidon Toy.toySpecSha in
/-- **Finding I1: `transact_connection` cannot be proved without `CircuitFacts`.** The
    code model accepts a withdrawal whose two input nullifiers are equal, every other
    hypothesis of `transact_connection` holds for it, and the spec's `transact` does not. -/
theorem transact_connection_fails_without_circuit : ¬ TransactConnectionWithoutCircuit := by
  intro h
  obtain ⟨s₁, s₂, s₃, e₂, e₃, h1, h2, h3, hdiff, outside⟩ := Toy.toy_dup_execution
  obtain ⟨-, -, -, -, -, hpid, -, hashes, solana, -, -⟩ := Toy.toy_execution
  have hspec := h Unit Unit Unit Toy.toyD Toy.toyRent Toy.toyS0
    s₂ s₃ _ Toy.toyTx Toy.dupA Toy.dupProof Toy.dupExt 0#u64 Toy.emptySlice Toy.emptySlice e₃ Toy.toyC
    Toy.toyLaws Toy.toyGenesis (.program h1 Toy.toyTx_rentPositive (.program h2 Toy.toyTx_rentPositive (.nil _))) Toy.toyDeploymentFacts
    (.program h3 Toy.toyTx_rentPositive (.nil _)) hashes solana ⟨hdiff⟩ outside
  unfold SpecTransactHolds at hspec
  obtain ⟨⟨-, -, -, -, -, -, hdistinct, -⟩, -⟩ := hspec
  exact hdistinct rfl

end Connection
